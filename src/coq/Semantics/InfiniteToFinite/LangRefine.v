From Coq Require Import
     Relations
     String
     List
     Lia
     ZArith
     Morphisms.

Require Import Coq.Logic.ProofIrrelevance.

From Vellvm Require Import
     Semantics.InterpretationStack
     Semantics.LLVMEvents
     Semantics.Denotation
     Semantics.MemoryAddress
     Semantics.Memory.Sizeof
     Semantics.Lang
     Semantics.InterpretationStack
     Semantics.TopLevel
     Semantics.DynamicValues
     Semantics.VellvmIntegers
     Semantics.LLVMParams
     Semantics.InfiniteToFinite.Conversions.BaseConversions
     Semantics.InfiniteToFinite.Conversions.DvalueConversions
     Semantics.InfiniteToFinite.Conversions.EventConversions
     Semantics.InfiniteToFinite.Conversions.TreeConversions
     Semantics.InfiniteToFinite.R2Injective
     Semantics.Memory.DvalueBytes
     Syntax.DynamicTypes
     Theory.TopLevelRefinements
     Theory.ContainsUB
     Utils.Error
     Utils.Monads
     Utils.MapMonadExtra
     Utils.PropT
     Utils.InterpProp
     Utils.InterpPropOOM
     Utils.ListUtil
     Utils.Tactics
     Utils.OOMRutt
     Utils.OOMRuttProps
     Utils.RuttPropsExtra
     Utils.AListFacts
     Utils.VellvmRelations
     Utils.ErrUbOomProp
     Utils.ErrOomPoison
     Utils.Oomable
     Utils.Poisonable
     Utils.NMaps
     Utils.IntMaps
     Handlers.MemoryModules.FiniteAddresses
     Handlers.MemoryModules.InfiniteAddresses
     Handlers.MemoryModelImplementation
     Handlers.SerializationTheory.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor.

From ITree Require Import
     ITree
     Basics
     Basics.HeterogeneousRelations
     Eq.Rutt
     Eq.RuttFacts
     Eq.Eqit
     Eq.EqAxiom.

Require Import Coq.Program.Equality.
Require Import Paco.paco.

Import InterpFacts.

Import MonadNotation.
Import ListNotations.
Import Classical.

(* TODO: Move these *)
Program Fixpoint Forall2_HInT {A B : Type}
  (xs : list A) (ys : list B) (R : forall a b, InT a xs -> InT b ys -> Prop) : Prop :=
  match xs, ys with
  | [], [] => True
  | (x::xs), (y::ys) =>
      R x y _ _ /\ Forall2_HInT xs ys (fun x y IN1 IN2 => R x y _ _)
  | _, _ =>
      False
  end.
Next Obligation.
  exact (inl eq_refl).
Defined.
Next Obligation.
  exact (inl eq_refl).
Defined.
Next Obligation.
  exact (inr IN1).
Defined.
Next Obligation.
  exact (inr IN2).
Defined.
Next Obligation.
  split. intros; intro C.
  intuition. inversion H.
  intro C. intuition. inversion H0.
Defined.
Next Obligation.
  split. intros; intro C.
  intuition. inversion H0.
  intro C. intuition. inversion H.
Defined.

(* Lemma map_monad_InT_oom_forall2 : *)
(*   forall {A B} l (f : forall (a : A), InT a l -> OOM B) res, *)
(*     map_monad_InT l f = NoOom res <-> *)
(*       Forall2_HInT l res (fun a b INA INB => f a INA = NoOom b). *)
(* Proof. *)
(*   intros A B. *)
(*   induction l; intros f res. *)
(*   - split; intros MAP. *)
(*     + cbn in *. *)
(*       inv MAP. *)
(*       auto. *)
(*     + cbn in *. *)
(*       break_match_hyp; tauto. *)
(*   - split; intros MAP. *)
(*     + rewrite map_monad_InT_unfold in MAP. *)
(*       cbn in *. *)
(*       break_match_hyp; inv MAP. *)
(*       break_match_hyp; inv H0. *)

(*       pose proof (IHl (fun (x : A) (HIn : InT x l) => f x (inr HIn)) l0) as FORALL. *)
(*       constructor; auto. *)
(*       eapply FORALL. eauto. *)
(*     + rewrite map_monad_InT_cons. *)
(*       cbn in *. *)
(*       break_match_hyp; try contradiction. *)
(*       cbn in *. *)
(*       destruct MAP as [FA MAP]. *)
(*       rewrite FA. *)

(*       pose proof (IHl (fun (x : A) (HIn : InT x l) => f x (inr HIn)) l0) as FORALL. *)
(*       apply FORALL in MAP. *)
(*       rewrite MAP. *)
(*       auto. *)
(* Qed. *)

Lemma Forall2_Forall2_HInT :
  forall {A B : Type} (xs : list A) (ys : list B) f,
    Forall2 f xs ys <->
    Forall2_HInT xs ys (fun a b HIna HInb => f a b).
Proof.
  intros A B xs ys f.
  split; intros H.
  - induction H; cbn; auto.
  - remember (xs, ys) as ZIP.
    replace xs with (fst ZIP) in H by (subst; cbn; auto).
    replace xs with (fst ZIP) by (subst; cbn; auto).
    replace ys with (snd ZIP) in H by (subst; cbn; auto).
    replace ys with (snd ZIP) by (subst; cbn; auto).
    clear HeqZIP xs ys.

    induction ZIP using double_list_rect;
      cbn in *; try contradiction.
    + constructor.
    + destruct H.
      constructor; eauto.
Qed.

Import VellvmIntegers.

(* TODO: Move this (FiniteIntptr.v) *)
Module Type VMemInt_Intptr_Properties (IP : INTPTR).
  (* No overflows *)
  Parameter madd_carry_zero :
    forall x y c,
      (@madd_carry _ IP.VMemInt_intptr x y c) = IP.zero.

  Parameter madd_overflow_zero :
    forall x y c,
      (@madd_overflow _ IP.VMemInt_intptr x y c) = IP.zero.

  Parameter msub_borrow_zero :
    forall x y c,
      (@msub_borrow _ IP.VMemInt_intptr x y c) = IP.zero.

  Parameter msub_overflow_zero :
    forall x y c,
      (@msub_overflow _ IP.VMemInt_intptr x y c) = IP.zero.

  (* Equality properties *)
  Parameter mequ_zero_one_false :
    @mequ _ IP.VMemInt_intptr IP.zero (@mone _ IP.VMemInt_intptr) = false.

  Parameter mequ_one_zero_false :
    @mequ _ IP.VMemInt_intptr (@mone _ IP.VMemInt_intptr) IP.zero = false.
End VMemInt_Intptr_Properties.

Module Type VMemInt_Refine (IP_INF : INTPTR) (IP_FIN : INTPTR).
  Parameter madd_refine :
    forall x_fin y_fin r_fin x_inf y_inf,
      IP_FIN.to_Z x_fin = IP_INF.to_Z x_inf ->
      IP_FIN.to_Z y_fin = IP_INF.to_Z y_inf ->
      @madd _ IP_FIN.VMemInt_intptr x_fin y_fin = NoOom r_fin ->
      exists r_inf,
        @madd _ IP_INF.VMemInt_intptr x_inf y_inf = NoOom r_inf /\
          IP_FIN.to_Z r_fin = IP_INF.to_Z r_inf.

  Parameter msub_refine :
    forall x_fin y_fin r_fin x_inf y_inf,
      IP_FIN.to_Z x_fin = IP_INF.to_Z x_inf ->
      IP_FIN.to_Z y_fin = IP_INF.to_Z y_inf ->
      @msub _ IP_FIN.VMemInt_intptr x_fin y_fin = NoOom r_fin ->
      exists r_inf,
        @msub _ IP_INF.VMemInt_intptr x_inf y_inf = NoOom r_inf /\
          IP_FIN.to_Z r_fin = IP_INF.to_Z r_inf.

  Parameter mmul_refine :
    forall x_fin y_fin r_fin x_inf y_inf,
      IP_FIN.to_Z x_fin = IP_INF.to_Z x_inf ->
      IP_FIN.to_Z y_fin = IP_INF.to_Z y_inf ->
      @mmul _ IP_FIN.VMemInt_intptr x_fin y_fin = NoOom r_fin ->
      exists r_inf,
        @mmul _ IP_INF.VMemInt_intptr x_inf y_inf = NoOom r_inf /\
          IP_FIN.to_Z r_fin = IP_INF.to_Z r_inf /\
          (@munsigned _ IP_INF.VMemInt_intptr x_inf * @munsigned _ IP_INF.VMemInt_intptr y_inf >? @munsigned _ IP_INF.VMemInt_intptr r_inf = false)%Z.

  Parameter mshl_refine :
    forall x_fin y_fin r_fin x_inf y_inf,
      IP_FIN.to_Z x_fin = IP_INF.to_Z x_inf ->
      IP_FIN.to_Z y_fin = IP_INF.to_Z y_inf ->
      @mshl _ IP_FIN.VMemInt_intptr x_fin y_fin = NoOom r_fin ->
      exists r_inf,
        @mshl _ IP_INF.VMemInt_intptr x_inf y_inf = NoOom r_inf /\
          IP_FIN.to_Z r_fin = IP_INF.to_Z r_inf.

  Parameter mdivu_refine :
    forall x_fin y_fin r_fin x_inf y_inf,
      IP_FIN.to_Z x_fin = IP_INF.to_Z x_inf ->
      IP_FIN.to_Z y_fin = IP_INF.to_Z y_inf ->
      @mdivu _ IP_FIN.VMemInt_intptr x_fin y_fin = r_fin ->
      exists r_inf,
        @mdivu _ IP_INF.VMemInt_intptr x_inf y_inf = r_inf /\
          IP_FIN.to_Z r_fin = IP_INF.to_Z r_inf.

  Parameter mdivs_refine :
    forall x_fin y_fin r_fin x_inf y_inf,
      IP_FIN.to_Z x_fin = IP_INF.to_Z x_inf ->
      IP_FIN.to_Z y_fin = IP_INF.to_Z y_inf ->
      @mdivs _ IP_FIN.VMemInt_intptr x_fin y_fin = NoOom r_fin ->
      exists r_inf,
        @mdivs _ IP_INF.VMemInt_intptr x_inf y_inf = NoOom r_inf /\
          IP_FIN.to_Z r_fin = IP_INF.to_Z r_inf.

  (* Parameter mshr_refine : *)
  (*   forall x_fin y_fin r_fin x_inf y_inf, *)
  (*     IP_FIN.to_Z x_fin = IP_INF.to_Z x_inf -> *)
  (*     IP_FIN.to_Z y_fin = IP_INF.to_Z y_inf -> *)
  (*     @mshr _ IP_FIN.VMemInt_intptr x_fin y_fin = r_fin -> *)
  (*     exists r_inf, *)
  (*       @mshr _ IP_INF.VMemInt_intptr x_inf y_inf = r_inf /\ *)
  (*         IP_FIN.to_Z r_fin = IP_INF.to_Z r_inf. *)

  Parameter mshru_refine :
    forall x_fin y_fin r_fin x_inf y_inf,
      IP_FIN.to_Z x_fin = IP_INF.to_Z x_inf ->
      IP_FIN.to_Z y_fin = IP_INF.to_Z y_inf ->
      @mshru _ IP_FIN.VMemInt_intptr x_fin y_fin = r_fin ->
      exists r_inf,
        @mshru _ IP_INF.VMemInt_intptr x_inf y_inf = r_inf /\
          IP_FIN.to_Z r_fin = IP_INF.to_Z r_inf.

  Parameter mmods_refine :
    forall x_fin y_fin r_fin x_inf y_inf,
      IP_FIN.to_Z x_fin = IP_INF.to_Z x_inf ->
      IP_FIN.to_Z y_fin = IP_INF.to_Z y_inf ->
      @mmods _ IP_FIN.VMemInt_intptr x_fin y_fin = NoOom r_fin ->
      exists r_inf,
        @mmods _ IP_INF.VMemInt_intptr x_inf y_inf = NoOom r_inf /\
          IP_FIN.to_Z r_fin = IP_INF.to_Z r_inf.

  Parameter mmodu_refine :
    forall x_fin y_fin r_fin x_inf y_inf,
      IP_FIN.to_Z x_fin = IP_INF.to_Z x_inf ->
      IP_FIN.to_Z y_fin = IP_INF.to_Z y_inf ->
      @mmodu _ IP_FIN.VMemInt_intptr x_fin y_fin = r_fin ->
      exists r_inf,
        @mmodu _ IP_INF.VMemInt_intptr x_inf y_inf = r_inf /\
          IP_FIN.to_Z r_fin = IP_INF.to_Z r_inf.

  Parameter mand_refine :
    forall x_fin y_fin r_fin x_inf y_inf,
      IP_FIN.to_Z x_fin = IP_INF.to_Z x_inf ->
      IP_FIN.to_Z y_fin = IP_INF.to_Z y_inf ->
      @mand _ IP_FIN.VMemInt_intptr x_fin y_fin = r_fin ->
      exists r_inf,
        @mand _ IP_INF.VMemInt_intptr x_inf y_inf = r_inf /\
          IP_FIN.to_Z r_fin = IP_INF.to_Z r_inf.

  Parameter mor_refine :
    forall x_fin y_fin r_fin x_inf y_inf,
      IP_FIN.to_Z x_fin = IP_INF.to_Z x_inf ->
      IP_FIN.to_Z y_fin = IP_INF.to_Z y_inf ->
      @mor _ IP_FIN.VMemInt_intptr x_fin y_fin = r_fin ->
      exists r_inf,
        @mor _ IP_INF.VMemInt_intptr x_inf y_inf = r_inf /\
          IP_FIN.to_Z r_fin = IP_INF.to_Z r_inf.

  Parameter mxor_refine :
    forall x_fin y_fin r_fin x_inf y_inf,
      IP_FIN.to_Z x_fin = IP_INF.to_Z x_inf ->
      IP_FIN.to_Z y_fin = IP_INF.to_Z y_inf ->
      @mxor _ IP_FIN.VMemInt_intptr x_fin y_fin = r_fin ->
      exists r_inf,
        @mxor _ IP_INF.VMemInt_intptr x_inf y_inf = r_inf /\
          IP_FIN.to_Z r_fin = IP_INF.to_Z r_inf.

  Parameter munsigned_refine :
    forall x_fin x_inf,
      IP_FIN.to_Z x_fin = IP_INF.to_Z x_inf ->
      @munsigned _ IP_FIN.VMemInt_intptr x_fin = @munsigned _ IP_INF.VMemInt_intptr x_inf.

  Parameter mrepr_refine :
    forall z x_fin x_inf,
      IP_FIN.to_Z x_fin = IP_INF.to_Z x_inf ->
      @mrepr _ IP_FIN.VMemInt_intptr z = NoOom x_fin ->
      @mrepr _ IP_INF.VMemInt_intptr z = NoOom x_inf.

  Parameter mcmpu_refine :
    forall icmp x_fin x_inf y_fin y_inf,
      IP_FIN.to_Z x_fin = IP_INF.to_Z x_inf ->
      IP_FIN.to_Z y_fin = IP_INF.to_Z y_inf ->
      @mcmpu _ IP_FIN.VMemInt_intptr icmp x_fin y_fin = @mcmpu _ IP_INF.VMemInt_intptr icmp x_inf y_inf.

End VMemInt_Refine.

Module VMemInt_Intptr_Properties_Inf : VMemInt_Intptr_Properties InterpreterStackBigIntptr.LP.IP.
  (* No overflows *)
  Lemma madd_carry_zero :
    forall x y c,
      (@madd_carry _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr x y c) = InterpreterStackBigIntptr.LP.IP.zero.
  Proof.
    intros x y c.
    cbn.
    setoid_rewrite InterpreterStackBigIntptr.LP.IP.to_Z_0.
    reflexivity.
  Qed.

  Lemma madd_overflow_zero :
    forall x y c,
      (@madd_overflow _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr x y c) = InterpreterStackBigIntptr.LP.IP.zero.
  Proof.
    intros x y c.
    cbn.
    setoid_rewrite InterpreterStackBigIntptr.LP.IP.to_Z_0.
    reflexivity.
  Qed.

  Lemma msub_borrow_zero :
    forall x y c,
      (@msub_borrow _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr x y c) = InterpreterStackBigIntptr.LP.IP.zero.
  Proof.
    intros x y c.
    cbn.
    setoid_rewrite InterpreterStackBigIntptr.LP.IP.to_Z_0.
    reflexivity.
  Qed.

  Lemma msub_overflow_zero :
    forall x y c,
      (@msub_overflow _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr x y c) = InterpreterStackBigIntptr.LP.IP.zero.
  Proof.
    intros x y c.
    cbn.
    setoid_rewrite InterpreterStackBigIntptr.LP.IP.to_Z_0.
    reflexivity.
  Qed.

  (* Equality properties *)
  Lemma mequ_zero_one_false :
    @mequ _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr InterpreterStackBigIntptr.LP.IP.zero (@mone _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr) = false.
  Proof.
    cbn; lia.
  Qed.

  Lemma mequ_one_zero_false :
    @mequ _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr (@mone _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr) InterpreterStackBigIntptr.LP.IP.zero = false.
  Proof.
    cbn; lia.
  Qed.

End VMemInt_Intptr_Properties_Inf.

Module VMemInt_Intptr_Properties_Fin : VMemInt_Intptr_Properties InterpreterStack64BitIntptr.LP.IP.
  (* No overflows *)
  Lemma madd_carry_zero :
    forall x y c,
      (@madd_carry _ InterpreterStack64BitIntptr.LP.IP.VMemInt_intptr x y c) = InterpreterStack64BitIntptr.LP.IP.zero.
  Proof.
    intros x y c.
    cbn.
    unfold InterpreterStack64BitIntptr.LP.IP.zero in *.
    reflexivity.
  Qed.

  Lemma madd_overflow_zero :
    forall x y c,
      (@madd_overflow _ InterpreterStack64BitIntptr.LP.IP.VMemInt_intptr x y c) = InterpreterStack64BitIntptr.LP.IP.zero.
  Proof.
    intros x y c.
    cbn.
    unfold InterpreterStack64BitIntptr.LP.IP.zero in *.
    reflexivity.
  Qed.

  Lemma msub_borrow_zero :
    forall x y c,
      (@msub_borrow _ InterpreterStack64BitIntptr.LP.IP.VMemInt_intptr x y c) = InterpreterStack64BitIntptr.LP.IP.zero.
  Proof.
    intros x y c.
    cbn.
    unfold InterpreterStack64BitIntptr.LP.IP.zero in *.
    reflexivity.
  Qed.

  Lemma msub_overflow_zero :
    forall x y c,
      (@msub_overflow _ InterpreterStack64BitIntptr.LP.IP.VMemInt_intptr x y c) = InterpreterStack64BitIntptr.LP.IP.zero.
  Proof.
    intros x y c.
    cbn.
    reflexivity.
  Qed.

  (* Equality properties *)
  Lemma mequ_zero_one_false :
    @mequ _ InterpreterStack64BitIntptr.LP.IP.VMemInt_intptr InterpreterStack64BitIntptr.LP.IP.zero (@mone _ InterpreterStack64BitIntptr.LP.IP.VMemInt_intptr) = false.
  Proof.
    cbn.
    reflexivity.
  Qed.

  Lemma mequ_one_zero_false :
    @mequ _ InterpreterStack64BitIntptr.LP.IP.VMemInt_intptr (@mone _ InterpreterStack64BitIntptr.LP.IP.VMemInt_intptr) InterpreterStack64BitIntptr.LP.IP.zero = false.
  Proof.
    cbn.
    reflexivity.
  Qed.

End VMemInt_Intptr_Properties_Fin.

Module VMemInt_Refine_InfFin : VMemInt_Refine InterpreterStackBigIntptr.LP.IP InterpreterStack64BitIntptr.LP.IP.
  Lemma madd_refine :
    forall x_fin y_fin r_fin x_inf y_inf,
      InterpreterStack64BitIntptr.LP.IP.to_Z x_fin = InterpreterStackBigIntptr.LP.IP.to_Z x_inf ->
      InterpreterStack64BitIntptr.LP.IP.to_Z y_fin = InterpreterStackBigIntptr.LP.IP.to_Z y_inf ->
      @madd _ InterpreterStack64BitIntptr.LP.IP.VMemInt_intptr x_fin y_fin = NoOom r_fin ->
      exists r_inf,
        @madd _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr x_inf y_inf = NoOom r_inf /\
          InterpreterStack64BitIntptr.LP.IP.to_Z r_fin = InterpreterStackBigIntptr.LP.IP.to_Z r_inf.
  Proof.
    intros x_fin y_fin r_fin x_inf y_inf X Y ADD.
    cbn.
    exists (x_inf + y_inf)%Z.
    split; auto.

    cbn in ADD.
    break_match_hyp_inv.

    unfold InterpreterStack64BitIntptr.LP.IP.to_Z, InterpreterStackBigIntptr.LP.IP.to_Z in *.
    rewrite Integers.add_unsigned.
    rewrite X, Y.
    rewrite Integers.unsigned_repr; eauto.

    (* TODO: Separate this into lemma? *)
    unfold Integers.add_carry in Heqb.
    cbn in Heqb.
    break_match_hyp; cbn in Heqb; try discriminate.

    subst.
    unfold Integers.max_unsigned.
    pose proof Integers.unsigned_range x_fin.
    pose proof Integers.unsigned_range y_fin.
    lia.
  Qed.

  Lemma msub_refine :
    forall x_fin y_fin r_fin x_inf y_inf,
      InterpreterStack64BitIntptr.LP.IP.to_Z x_fin = InterpreterStackBigIntptr.LP.IP.to_Z x_inf ->
      InterpreterStack64BitIntptr.LP.IP.to_Z y_fin = InterpreterStackBigIntptr.LP.IP.to_Z y_inf ->
      @msub _ InterpreterStack64BitIntptr.LP.IP.VMemInt_intptr x_fin y_fin = NoOom r_fin ->
      exists r_inf,
        @msub _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr x_inf y_inf = NoOom r_inf /\
          InterpreterStack64BitIntptr.LP.IP.to_Z r_fin = InterpreterStackBigIntptr.LP.IP.to_Z r_inf.
  Proof.
    intros x_fin y_fin r_fin x_inf y_inf X Y SUB.
    cbn.
    exists (x_inf - y_inf)%Z.
    split; auto.

    cbn in SUB.
    break_match_hyp_inv.
    unfold Integers.sub.
    unfold InterpreterStack64BitIntptr.LP.IP.to_Z, InterpreterStackBigIntptr.LP.IP.to_Z in *.
    subst.
    rewrite Integers.unsigned_repr; eauto.
    unfold Integers.max_unsigned.
    pose proof Integers.unsigned_range x_fin.
    pose proof Integers.unsigned_range y_fin.
    lia.
  Qed.

  Lemma mmul_refine :
    forall x_fin y_fin r_fin x_inf y_inf,
      InterpreterStack64BitIntptr.LP.IP.to_Z x_fin = InterpreterStackBigIntptr.LP.IP.to_Z x_inf ->
      InterpreterStack64BitIntptr.LP.IP.to_Z y_fin = InterpreterStackBigIntptr.LP.IP.to_Z y_inf ->
      @mmul _ InterpreterStack64BitIntptr.LP.IP.VMemInt_intptr x_fin y_fin = NoOom r_fin ->
      exists r_inf,
        @mmul _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr x_inf y_inf = NoOom r_inf /\
          InterpreterStack64BitIntptr.LP.IP.to_Z r_fin = InterpreterStackBigIntptr.LP.IP.to_Z r_inf /\
          (@munsigned _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr x_inf * @munsigned _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr y_inf >? @munsigned _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr r_inf = false)%Z.
  Proof.
    intros x_fin y_fin r_fin x_inf y_inf X Y MUL.
    exists (x_inf * y_inf)%Z.
    split; auto.

    Opaque Integers.modulus.
    cbn in MUL.
    break_match_hyp_inv.

    unfold InterpreterStack64BitIntptr.LP.IP.to_Z, InterpreterStackBigIntptr.LP.IP.to_Z in *.
    subst.
    pose proof Integers.unsigned_range x_fin.
    pose proof Integers.unsigned_range y_fin.
    rewrite Integers.unsigned_repr; eauto.
    2: lia.
    split; auto.
    unfold munsigned.
    cbn.
    lia.
  Qed.

  Lemma mshl_refine :
    forall x_fin y_fin r_fin x_inf y_inf,
      InterpreterStack64BitIntptr.LP.IP.to_Z x_fin = InterpreterStackBigIntptr.LP.IP.to_Z x_inf ->
      InterpreterStack64BitIntptr.LP.IP.to_Z y_fin = InterpreterStackBigIntptr.LP.IP.to_Z y_inf ->
      @mshl _ InterpreterStack64BitIntptr.LP.IP.VMemInt_intptr x_fin y_fin = NoOom r_fin ->
      exists r_inf,
        @mshl _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr x_inf y_inf = NoOom r_inf /\
          InterpreterStack64BitIntptr.LP.IP.to_Z r_fin = InterpreterStackBigIntptr.LP.IP.to_Z r_inf.
  Proof.
    intros x_fin y_fin r_fin x_inf y_inf X Y SHL.
    cbn.
    exists (Z.shiftl x_inf y_inf).

    cbn in SHL.
    split; auto.
    break_match_hyp_inv.

    unfold InterpreterStack64BitIntptr.LP.IP.to_Z, InterpreterStackBigIntptr.LP.IP.to_Z in *.
    subst.
    pose proof Integers.unsigned_range x_fin.
    pose proof Integers.unsigned_range y_fin.
    rewrite Integers.unsigned_repr; eauto.
    unfold Integers.max_unsigned in *.
    split; try lia.
    apply Z.shiftl_nonneg; lia.
  Qed.

  Lemma mdivu_refine :
    forall x_fin y_fin r_fin x_inf y_inf,
      InterpreterStack64BitIntptr.LP.IP.to_Z x_fin = InterpreterStackBigIntptr.LP.IP.to_Z x_inf ->
      InterpreterStack64BitIntptr.LP.IP.to_Z y_fin = InterpreterStackBigIntptr.LP.IP.to_Z y_inf ->
      @mdivu _ InterpreterStack64BitIntptr.LP.IP.VMemInt_intptr x_fin y_fin = r_fin ->
      exists r_inf,
        @mdivu _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr x_inf y_inf = r_inf /\
          InterpreterStack64BitIntptr.LP.IP.to_Z r_fin = InterpreterStackBigIntptr.LP.IP.to_Z r_inf.
  Proof.
    intros x_fin y_fin r_fin x_inf y_inf X Y DIV.
    cbn.
    exists (x_inf / y_inf)%Z.
    split; auto.

    cbn in DIV.
    subst.

    unfold InterpreterStack64BitIntptr.LP.IP.to_Z, InterpreterStackBigIntptr.LP.IP.to_Z in *.
    subst.
    pose proof Integers.unsigned_range x_fin.
    pose proof Integers.unsigned_range y_fin.
    unfold Integers.divu.
    rewrite Integers.unsigned_repr; auto.
    split; try lia.
    apply Z_div_nonneg_nonneg; try lia.
    unfold Integers.max_unsigned.
    pose proof Z.div_lt (Integers.unsigned x_fin) (Integers.unsigned y_fin).
    assert (Integers.unsigned x_fin = 0 \/ 0 < Integers.unsigned x_fin)%Z as [X_FIN | X_FIN] by lia.
    - rewrite X_FIN.
      cbn. lia.
    - forward H1; try lia.
      assert (Integers.unsigned y_fin = 0 \/ Integers.unsigned y_fin = 1 \/ 1 < Integers.unsigned y_fin)%Z as [Y_FIN | [Y_FIN | Y_FIN]] by lia.
      + rewrite Y_FIN.
        rewrite Zdiv_0_r.
        lia.
      + rewrite Y_FIN.
        rewrite Z.div_1_r.
        lia.
      + lia.
  Qed.

  Lemma mdivs_refine :
    forall x_fin y_fin r_fin x_inf y_inf,
      InterpreterStack64BitIntptr.LP.IP.to_Z x_fin = InterpreterStackBigIntptr.LP.IP.to_Z x_inf ->
      InterpreterStack64BitIntptr.LP.IP.to_Z y_fin = InterpreterStackBigIntptr.LP.IP.to_Z y_inf ->
      @mdivs _ InterpreterStack64BitIntptr.LP.IP.VMemInt_intptr x_fin y_fin = NoOom r_fin ->
      exists r_inf,
        @mdivs _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr x_inf y_inf = NoOom r_inf /\
          InterpreterStack64BitIntptr.LP.IP.to_Z r_fin = InterpreterStackBigIntptr.LP.IP.to_Z r_inf.
  Proof.
    intros x_fin y_fin r_fin x_inf y_inf X Y DIV.
    cbn in DIV; inv DIV.
  Qed.

  Lemma mshru_refine :
    forall x_fin y_fin r_fin x_inf y_inf,
      InterpreterStack64BitIntptr.LP.IP.to_Z x_fin = InterpreterStackBigIntptr.LP.IP.to_Z x_inf ->
      InterpreterStack64BitIntptr.LP.IP.to_Z y_fin = InterpreterStackBigIntptr.LP.IP.to_Z y_inf ->
      @mshru _ InterpreterStack64BitIntptr.LP.IP.VMemInt_intptr x_fin y_fin = r_fin ->
      exists r_inf,
        @mshru _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr x_inf y_inf = r_inf /\
          InterpreterStack64BitIntptr.LP.IP.to_Z r_fin = InterpreterStackBigIntptr.LP.IP.to_Z r_inf.
  Proof.
    intros x_fin y_fin r_fin x_inf y_inf X Y SHR.
    cbn.
    exists (Z.shiftr x_inf y_inf).
    split; auto.

    cbn in SHR.
    subst.

    unfold InterpreterStack64BitIntptr.LP.IP.to_Z, InterpreterStackBigIntptr.LP.IP.to_Z in *.
    subst.
    pose proof Integers.unsigned_range x_fin.
    pose proof Integers.unsigned_range y_fin.
    unfold Integers.shru.
    rewrite Integers.unsigned_repr; auto.
    unfold Integers.max_unsigned.
    split.
    - apply Z.shiftr_nonneg; lia.
    - rewrite Integers.Zshiftr_div_two_p; try lia.
    pose proof Z.div_lt (Integers.unsigned x_fin) (Integers.unsigned y_fin).
    assert (Integers.unsigned x_fin = 0 \/ 0 < Integers.unsigned x_fin)%Z as [X_FIN | X_FIN] by lia.
    -- rewrite X_FIN.
      cbn. lia.
    -- forward H1; try lia.
      assert (Integers.unsigned y_fin = 0 \/ Integers.unsigned y_fin = 1 \/ 1 < Integers.unsigned y_fin)%Z as [Y_FIN | [Y_FIN | Y_FIN]] by lia.
      + rewrite Y_FIN.
        cbn.
        rewrite Z.div_1_r.
        lia.
      + rewrite Y_FIN.
        assert (two_p 1 = 2)%Z.
        { unfold two_p.
          rewrite two_power_pos_correct. lia.
        }
        rewrite H2.
        pose proof Z.div_le_upper_bound (Integers.unsigned x_fin) 2 (@Integers.modulus 64 - 1).
        forward H3; [lia|].
        forward H3; [lia|].
        auto.
      + forward H1.
        lia.
        pose proof Z.div_le_upper_bound (Integers.unsigned x_fin) (two_p (Integers.unsigned y_fin)) (@Integers.modulus 64 - 1).
        forward H2.
        { unfold two_p.
          break_match_goal; try lia.
          rewrite two_power_pos_correct; lia.
        }
        forward H2.
        { unfold two_p.
          break_match_goal; try lia.
          rewrite two_power_pos_correct.
          assert (1 <= Z.pow_pos 2 p)%Z.
          { lia.
          }
          pose proof Z.mul_le_mono_nonneg_r 1 (Z.pow_pos 2 p) (@Integers.modulus 64 - 1).
          forward H4; [lia|].
          forward H4; [lia|].
          lia.
        }
        auto.
  Qed.

  Lemma mmods_refine :
    forall x_fin y_fin r_fin x_inf y_inf,
      InterpreterStack64BitIntptr.LP.IP.to_Z x_fin = InterpreterStackBigIntptr.LP.IP.to_Z x_inf ->
      InterpreterStack64BitIntptr.LP.IP.to_Z y_fin = InterpreterStackBigIntptr.LP.IP.to_Z y_inf ->
      @mmods _ InterpreterStack64BitIntptr.LP.IP.VMemInt_intptr x_fin y_fin = NoOom r_fin ->
      exists r_inf,
        @mmods _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr x_inf y_inf = NoOom r_inf /\
          InterpreterStack64BitIntptr.LP.IP.to_Z r_fin = InterpreterStackBigIntptr.LP.IP.to_Z r_inf.
  Proof.
    intros x_fin y_fin r_fin x_inf y_inf X Y MOD.
    cbn in MOD; inv MOD.
  Qed.

  Lemma mmodu_refine :
    forall x_fin y_fin r_fin x_inf y_inf,
      InterpreterStack64BitIntptr.LP.IP.to_Z x_fin = InterpreterStackBigIntptr.LP.IP.to_Z x_inf ->
      InterpreterStack64BitIntptr.LP.IP.to_Z y_fin = InterpreterStackBigIntptr.LP.IP.to_Z y_inf ->
      @mmodu _ InterpreterStack64BitIntptr.LP.IP.VMemInt_intptr x_fin y_fin = r_fin ->
      exists r_inf,
        @mmodu _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr x_inf y_inf = r_inf /\
          InterpreterStack64BitIntptr.LP.IP.to_Z r_fin = InterpreterStackBigIntptr.LP.IP.to_Z r_inf.
  Proof.
    intros x_fin y_fin r_fin x_inf y_inf X Y MOD.
    cbn.
    exists (x_inf mod y_inf)%Z.
    split; auto.

    cbn in MOD.
    subst.

    unfold InterpreterStack64BitIntptr.LP.IP.to_Z, InterpreterStackBigIntptr.LP.IP.to_Z in *.
    subst.
    unfold Integers.modu.
    rewrite Integers.unsigned_repr; try lia.
    unfold Integers.max_unsigned.

    pose proof Integers.unsigned_range x_fin.
    pose proof Integers.unsigned_range y_fin.
    destruct (Z.eq_dec (Integers.unsigned y_fin) 0%Z).
    { (* y_fin = 0 *)
      rewrite e.
      rewrite Zmod_0_r.
      lia.
    }

    pose proof Z.mod_bound_or (Integers.unsigned x_fin) (Integers.unsigned y_fin).
    forward H1; auto.
    lia.
  Qed.

  (* TODO: Move this *)
  Lemma Zland_range :
    forall a b c,
      (0 <= a < two_power_nat c)%Z ->
      (0 <= b < two_power_nat c)%Z ->
      (0 <= Z.land a b < two_power_nat c)%Z.
  Proof.
    intros a b c A B.
    pose proof Z.land_nonneg a b as [_ N].
    forward N; [lia|].
    split; try lia.
    pose proof (Z.log2_land a b).
    repeat (forward H; [lia|]).
    assert (Z.log2 (Z.land a b) <= Z.max (Z.log2 a) (Z.log2 b))%Z as LT by lia.
    assert (a = 0 \/ 0 < a)%Z as [ZERO | POS] by lia.
    - subst.
      rewrite Z.land_0_l in *.
      lia.
    - assert (b = 0 \/ 0 < b)%Z as [ZEROb | POSb] by lia.
      + subst.
        rewrite Z.land_0_r in *.
        lia.
      + assert (Z.land a b = 0 \/ Z.land a b <> 0)%Z as [EQZ | NZ] by lia.
        lia.

        pose proof (two_p_correct (Z.of_nat c)) as POW.
        rewrite <- Coqlib.two_power_nat_two_p in POW.
        pose proof Z.log2_lt_pow2 a (Z.of_nat c) POS as [aBOUND _].
        pose proof Z.log2_lt_pow2 b (Z.of_nat c) POSb as [bBOUND _].
        forward aBOUND; [lia|].
        forward bBOUND; [lia|].
        eapply Z.max_le in LT.
        rewrite POW.
        eapply Z.log2_lt_pow2; lia.
  Qed.

  (* TODO: Move this *)
  Lemma Zlor_range :
    forall a b c,
      (0 <= a < two_power_nat c)%Z ->
      (0 <= b < two_power_nat c)%Z ->
      (0 <= Z.lor a b < two_power_nat c)%Z.
  Proof.
    intros a b c A B.
    pose proof Z.lor_nonneg a b as [_ N].
    forward N; [lia|].
    split; try lia.
    pose proof (Z.log2_lor a b).
    repeat (forward H; [lia|]).
    assert (Z.log2 (Z.lor a b) <= Z.max (Z.log2 a) (Z.log2 b))%Z as LT by lia.
    assert (a = 0 \/ 0 < a)%Z as [ZERO | POS] by lia.
    - subst.
      rewrite Z.lor_0_l in *.
      lia.
    - assert (b = 0 \/ 0 < b)%Z as [ZEROb | POSb] by lia.
      + subst.
        rewrite Z.lor_0_r in *.
        lia.
      + assert (Z.lor a b <> 0%Z) as NZ.
        { intros CONTRA.
          eapply Z.lor_eq_0_iff in CONTRA.
          lia.
        }
        pose proof (two_p_correct (Z.of_nat c)) as POW.
        rewrite <- Coqlib.two_power_nat_two_p in POW.
        pose proof Z.log2_lt_pow2 a (Z.of_nat c) POS as [aBOUND _].
        pose proof Z.log2_lt_pow2 b (Z.of_nat c) POSb as [bBOUND _].
        forward aBOUND; [lia|].
        forward bBOUND; [lia|].
        eapply Z.max_le in LT.
        rewrite POW.
        eapply Z.log2_lt_pow2; lia.
  Qed.

  (* TODO: Move this *)
  Lemma Zlxor_range :
    forall a b c,
      (0 <= a < two_power_nat c)%Z ->
      (0 <= b < two_power_nat c)%Z ->
      (0 <= Z.lxor a b < two_power_nat c)%Z.
  Proof.
    intros a b c A B.
    pose proof Z.lxor_nonneg a b as [_ N].
    forward N; [lia|].
    split; try lia.
    pose proof (Z.log2_lxor a b).
    repeat (forward H; [lia|]).
    assert (Z.log2 (Z.lxor a b) <= Z.max (Z.log2 a) (Z.log2 b))%Z as LT by lia.
    assert (a = 0 \/ 0 < a)%Z as [ZERO | POS] by lia.
    - subst.
      rewrite Z.lxor_0_l in *.
      lia.
    - assert (b = 0 \/ 0 < b)%Z as [ZEROb | POSb] by lia.
      + subst.
        rewrite Z.lxor_0_r in *.
        lia.
      + assert (Z.lxor a b = 0 \/ Z.lxor a b <> 0)%Z as [EQZ | NZ] by lia.
        lia.

        pose proof (two_p_correct (Z.of_nat c)) as POW.
        rewrite <- Coqlib.two_power_nat_two_p in POW.
        pose proof Z.log2_lt_pow2 a (Z.of_nat c) POS as [aBOUND _].
        pose proof Z.log2_lt_pow2 b (Z.of_nat c) POSb as [bBOUND _].
        forward aBOUND; [lia|].
        forward bBOUND; [lia|].
        eapply Z.max_le in LT.
        rewrite POW.
        eapply Z.log2_lt_pow2; lia.
  Qed.

  Lemma mand_refine :
    forall x_fin y_fin r_fin x_inf y_inf,
      InterpreterStack64BitIntptr.LP.IP.to_Z x_fin = InterpreterStackBigIntptr.LP.IP.to_Z x_inf ->
      InterpreterStack64BitIntptr.LP.IP.to_Z y_fin = InterpreterStackBigIntptr.LP.IP.to_Z y_inf ->
      @mand _ InterpreterStack64BitIntptr.LP.IP.VMemInt_intptr x_fin y_fin = r_fin ->
      exists r_inf,
        @mand _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr x_inf y_inf = r_inf /\
          InterpreterStack64BitIntptr.LP.IP.to_Z r_fin = InterpreterStackBigIntptr.LP.IP.to_Z r_inf.
  Proof.
    intros x_fin y_fin r_fin x_inf y_inf X Y AND.
    cbn.
    exists (Z.land x_inf y_inf).
    split; auto.

    cbn in AND.
    unfold Integers.and in AND.
    subst.

    unfold InterpreterStack64BitIntptr.LP.IP.to_Z, InterpreterStackBigIntptr.LP.IP.to_Z in *.
    subst.
    pose proof Integers.unsigned_range x_fin.
    pose proof Integers.unsigned_range y_fin.
    rewrite Integers.unsigned_repr; auto.
    unfold Integers.max_unsigned.
    pose proof Z.log2_land (Integers.unsigned x_fin) (Integers.unsigned y_fin).
    repeat (forward H1; [lia|]).

    Transparent Integers.modulus.
    unfold Integers.modulus in *.
    rewrite two_power_pos_nat in H, H0.
    rewrite two_power_pos_nat.
    pose proof Zland_range _ _ _ H H0.
    Opaque Integers.modulus.
    lia.
  Qed.

  Lemma mor_refine :
    forall x_fin y_fin r_fin x_inf y_inf,
      InterpreterStack64BitIntptr.LP.IP.to_Z x_fin = InterpreterStackBigIntptr.LP.IP.to_Z x_inf ->
      InterpreterStack64BitIntptr.LP.IP.to_Z y_fin = InterpreterStackBigIntptr.LP.IP.to_Z y_inf ->
      @mor _ InterpreterStack64BitIntptr.LP.IP.VMemInt_intptr x_fin y_fin = r_fin ->
      exists r_inf,
        @mor _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr x_inf y_inf = r_inf /\
          InterpreterStack64BitIntptr.LP.IP.to_Z r_fin = InterpreterStackBigIntptr.LP.IP.to_Z r_inf.
  Proof.
    intros x_fin y_fin r_fin x_inf y_inf X Y OR.
    cbn.
    exists (Z.lor x_inf y_inf).
    split; auto.

    cbn in OR.
    unfold Integers.or in OR.
    subst.

    unfold InterpreterStack64BitIntptr.LP.IP.to_Z, InterpreterStackBigIntptr.LP.IP.to_Z in *.
    subst.
    pose proof Integers.unsigned_range x_fin.
    pose proof Integers.unsigned_range y_fin.
    rewrite Integers.unsigned_repr; auto.
    unfold Integers.max_unsigned.
    pose proof Z.log2_lor (Integers.unsigned x_fin) (Integers.unsigned y_fin).
    repeat (forward H1; [lia|]).

    Transparent Integers.modulus.
    unfold Integers.modulus in *.
    rewrite two_power_pos_nat in H, H0.
    rewrite two_power_pos_nat.
    pose proof Zlor_range _ _ _ H H0.
    Opaque Integers.modulus.
    lia.
  Qed.

  Lemma mxor_refine :
    forall x_fin y_fin r_fin x_inf y_inf,
      InterpreterStack64BitIntptr.LP.IP.to_Z x_fin = InterpreterStackBigIntptr.LP.IP.to_Z x_inf ->
      InterpreterStack64BitIntptr.LP.IP.to_Z y_fin = InterpreterStackBigIntptr.LP.IP.to_Z y_inf ->
      @mxor _ InterpreterStack64BitIntptr.LP.IP.VMemInt_intptr x_fin y_fin = r_fin ->
      exists r_inf,
        @mxor _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr x_inf y_inf = r_inf /\
          InterpreterStack64BitIntptr.LP.IP.to_Z r_fin = InterpreterStackBigIntptr.LP.IP.to_Z r_inf.
  Proof.
    intros x_fin y_fin r_fin x_inf y_inf X Y XOR.
    cbn.
    exists (Z.lxor x_inf y_inf).
    split; auto.

    cbn in XOR.
    unfold Integers.xor in XOR.
    subst.

    unfold InterpreterStack64BitIntptr.LP.IP.to_Z, InterpreterStackBigIntptr.LP.IP.to_Z in *.
    subst.
    pose proof Integers.unsigned_range x_fin.
    pose proof Integers.unsigned_range y_fin.
    rewrite Integers.unsigned_repr; auto.
    unfold Integers.max_unsigned.
    pose proof Z.log2_lxor (Integers.unsigned x_fin) (Integers.unsigned y_fin).
    repeat (forward H1; [lia|]).

    Transparent Integers.modulus.
    unfold Integers.modulus in *.
    rewrite two_power_pos_nat in H, H0.
    rewrite two_power_pos_nat.
    pose proof Zlxor_range _ _ _ H H0.
    Opaque Integers.modulus.
    lia.
  Qed.

  Lemma munsigned_refine :
    forall x_fin x_inf,
      InterpreterStack64BitIntptr.LP.IP.to_Z x_fin = InterpreterStackBigIntptr.LP.IP.to_Z x_inf ->
      @munsigned _ InterpreterStack64BitIntptr.LP.IP.VMemInt_intptr x_fin = @munsigned _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr x_inf.
  Proof.
    intros x_fin x_inf TOZ.
    cbn in *.
    unfold InterpreterStackBigIntptr.LP.IP.to_Z, InterpreterStack64BitIntptr.LP.IP.to_Z in *.
    auto.
  Qed.

  Lemma mrepr_refine :
    forall z x_fin x_inf,
      InterpreterStack64BitIntptr.LP.IP.to_Z x_fin = InterpreterStackBigIntptr.LP.IP.to_Z x_inf ->
      @mrepr _ InterpreterStack64BitIntptr.LP.IP.VMemInt_intptr z = NoOom x_fin ->
      @mrepr _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr z = NoOom x_inf.
  Proof.
    intros z x_fin x_inf H H0.
    cbn.
    rewrite IP64Bit.VMemInt_intptr_mrepr_from_Z in H0.
    erewrite FiniteIntptr.IP64Bit.from_Z_to_Z in H; eauto.
    subst.
    reflexivity.
  Qed.

  Lemma mcmpu_refine :
    forall icmp x_fin x_inf y_fin y_inf,
      InterpreterStack64BitIntptr.LP.IP.to_Z x_fin = InterpreterStackBigIntptr.LP.IP.to_Z x_inf ->
      InterpreterStack64BitIntptr.LP.IP.to_Z y_fin = InterpreterStackBigIntptr.LP.IP.to_Z y_inf ->
      @mcmpu _ InterpreterStack64BitIntptr.LP.IP.VMemInt_intptr icmp x_fin y_fin = @mcmpu _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr icmp x_inf y_inf.
  Proof.
    intros icmp x_fin x_inf y_fin y_inf X Y.
    unfold InterpreterStack64BitIntptr.LP.IP.to_Z,
      InterpreterStackBigIntptr.LP.IP.to_Z in *;
      subst.

    destruct icmp;
      cbn in *.
    - (* eq *)
      pose proof Integers.eq_spec x_fin y_fin.
      break_match_hyp; subst.
      + rewrite Z.eqb_refl; auto.
      + symmetry; apply Z.eqb_neq.
        intros CONTRA.
        destruct x_fin, y_fin.
        cbn in *; subst.
        unfold Integers.eq in Heqb.
        cbn in *.
        rewrite Coqlib.zeq_true in Heqb; inv Heqb.
    - (* ne *)
      pose proof Integers.eq_spec x_fin y_fin.
      break_match_hyp; subst; cbn;
        unfold Zneq_bool.
      + rewrite Z.compare_refl; auto.
      + break_match_goal; auto.
        apply Z.compare_eq in Heqc.
        destruct x_fin, y_fin; cbn in *; subst; cbn in *.
        unfold Integers.eq in Heqb.
        cbn in *.
        rewrite Coqlib.zeq_true in Heqb; inv Heqb.
    - (* lt *)
      unfold Integers.ltu.
      break_match_goal; lia.
    - (* le *)
      unfold Integers.ltu.
      break_match_goal; lia.
    - (* gt *)
      unfold Integers.ltu.
      break_match_goal; lia.
    - (* ge *)
      unfold Integers.ltu.
      break_match_goal; lia.
  Qed.

End VMemInt_Refine_InfFin.

Module Type Sizeof_Refine (SZ_INF : Sizeof) (SZ_FIN : Sizeof).
  Parameter bit_sizeof_dtyp_fin_inf :
    forall t,
      SZ_INF.bit_sizeof_dtyp t = SZ_FIN.bit_sizeof_dtyp t.

  Parameter sizeof_dtyp_fin_inf :
    forall t,
      SZ_INF.sizeof_dtyp t = SZ_FIN.sizeof_dtyp t.

  Parameter dtyp_alignment_fin_inf :
    forall t,
      SZ_INF.dtyp_alignment t = SZ_FIN.dtyp_alignment t.

  Parameter max_preferred_dtyp_alignment_fin_inf :
    forall dts,
      SZ_INF.max_preferred_dtyp_alignment dts = SZ_FIN.max_preferred_dtyp_alignment dts.
End Sizeof_Refine.

Module Sizeof_Refine_InfFin : Sizeof_Refine InterpreterStackBigIntptr.LP.SIZEOF InterpreterStack64BitIntptr.LP.SIZEOF.
  Lemma bit_sizeof_dtyp_fin_inf :
    forall t,
      InterpreterStackBigIntptr.LP.SIZEOF.bit_sizeof_dtyp t = InterpreterStack64BitIntptr.LP.SIZEOF.bit_sizeof_dtyp t.
  Proof.
    intros t.
    unfold InterpreterStackBigIntptr.LP.SIZEOF.bit_sizeof_dtyp.
    reflexivity.
  Qed.

  Lemma sizeof_dtyp_fin_inf :
    forall t,
      InterpreterStackBigIntptr.LP.SIZEOF.sizeof_dtyp t = InterpreterStack64BitIntptr.LP.SIZEOF.sizeof_dtyp t.
  Proof.
    reflexivity.
  Qed.

  Lemma dtyp_alignment_fin_inf :
    forall t,
      InterpreterStackBigIntptr.LP.SIZEOF.dtyp_alignment t = InterpreterStack64BitIntptr.LP.SIZEOF.dtyp_alignment t.
  Proof.
    reflexivity.
  Qed.

  Lemma max_preferred_dtyp_alignment_fin_inf :
    forall dts,
      InterpreterStackBigIntptr.LP.SIZEOF.max_preferred_dtyp_alignment dts = InterpreterStack64BitIntptr.LP.SIZEOF.max_preferred_dtyp_alignment dts.
  Proof.
    reflexivity.
  Qed.

End Sizeof_Refine_InfFin.

Module Type ItoP_Refine (IS1 : InterpreterStack) (IS2 : InterpreterStack) (AC1 : AddrConvert IS1.LP.ADDR IS1.LP.PTOI IS2.LP.ADDR IS2.LP.PTOI) (AC2 : AddrConvert IS2.LP.ADDR IS2.LP.PTOI IS1.LP.ADDR IS1.LP.PTOI).
  Parameter addr_convert_int_to_ptr :
    forall base_addr_fin base_addr_inf res_addr_fin res_addr_inf z
      (CONV_BASE : AC2.addr_convert base_addr_fin = NoOom base_addr_inf)
      (CONV_RES : AC2.addr_convert res_addr_fin = NoOom res_addr_inf)
      (ITP : IS2.LP.ITOP.int_to_ptr z (IS2.LP.PROV.address_provenance base_addr_fin) = NoOom res_addr_fin),
      (IS1.LP.ITOP.int_to_ptr z (IS1.LP.PROV.address_provenance base_addr_inf)) = ret res_addr_inf.

  Parameter int_to_ptr_fin_inf :
    forall z prov prov' a_fin a_inf,
      AC2.addr_convert a_fin = NoOom a_inf ->
      IS1.LP.PROV.address_provenance a_inf = prov' ->
      IS2.LP.ITOP.int_to_ptr z prov = NoOom a_fin ->
      IS1.LP.ITOP.int_to_ptr z prov' = NoOom a_inf.

  Parameter int_to_ptr_fin_inf_wildcard :
    forall z a_fin a_inf,
      AC2.addr_convert a_fin = NoOom a_inf ->
      IS2.LP.ITOP.int_to_ptr z IS2.LP.PROV.wildcard_prov = NoOom a_fin ->
      IS1.LP.ITOP.int_to_ptr z IS1.LP.PROV.wildcard_prov = NoOom a_inf.
End ItoP_Refine.

Module ItoP_Refine_InfFin : ItoP_Refine InterpreterStackBigIntptr InterpreterStack64BitIntptr InfToFinAddrConvert FinToInfAddrConvert.
  Lemma addr_convert_int_to_ptr :
    forall base_addr_fin base_addr_inf res_addr_fin res_addr_inf z
      (CONV_BASE : FinToInfAddrConvert.addr_convert base_addr_fin = NoOom base_addr_inf)
      (CONV_RES : FinToInfAddrConvert.addr_convert res_addr_fin = NoOom res_addr_inf)
      (ITP : InterpreterStack64BitIntptr.LP.ITOP.int_to_ptr z (InterpreterStack64BitIntptr.LP.PROV.address_provenance base_addr_fin) = NoOom res_addr_fin),
      (InterpreterStackBigIntptr.LP.ITOP.int_to_ptr z (InterpreterStackBigIntptr.LP.PROV.address_provenance base_addr_inf)) = ret res_addr_inf.
  Proof.
    intros base_addr_fin base_addr_inf res_addr_fin res_addr_inf z CONV_BASE CONV_RES ITP.
    cbn in *.
    unfold InterpreterStack64BitIntptr.LP.ITOP.int_to_ptr in *.
    break_match_hyp_inv.
    unfold FinToInfAddrConvert.addr_convert in *.
    cbn in *.
    inv CONV_RES.

    unfold InterpreterStackBigIntptr.LP.PROV.address_provenance.
    unfold InterpreterStack64BitIntptr.LP.PROV.address_provenance.
    destruct base_addr_fin; inv CONV_BASE; cbn.

    rewrite Integers.Z_mod_modulus_eq.
    rewrite Coqlib.Zmod_small; try lia; auto.
  Qed.

  Lemma int_to_ptr_fin_inf :
    forall z prov prov' a_fin a_inf,
      FinToInfAddrConvert.addr_convert a_fin = NoOom a_inf ->
      InterpreterStackBigIntptr.LP.PROV.address_provenance a_inf = prov' ->
      InterpreterStack64BitIntptr.LP.ITOP.int_to_ptr z prov = NoOom a_fin ->
      InterpreterStackBigIntptr.LP.ITOP.int_to_ptr z prov' = NoOom a_inf.
  Proof.
    intros z prov prov' a_fin a_inf CONV PROV ITP.
    destruct a_fin.
    cbn in CONV; inv CONV.
    cbn in *.
    unfold InterpreterStack64BitIntptr.LP.ITOP.int_to_ptr in ITP.
    break_match_hyp_inv.
    rewrite Integers.unsigned_repr.
    2: {
      unfold Integers.max_unsigned.
      lia.
    }
    auto.
  Qed.

  Lemma int_to_ptr_fin_inf_wildcard :
    forall z a_fin a_inf,
      FinToInfAddrConvert.addr_convert a_fin = NoOom a_inf ->
      InterpreterStack64BitIntptr.LP.ITOP.int_to_ptr z FinPROV.wildcard_prov = NoOom a_fin ->
      InterpreterStackBigIntptr.LP.ITOP.int_to_ptr z InfPROV.wildcard_prov = NoOom a_inf.
  Proof.
    intros z a_fin a_inf CONV ITP.
    destruct a_fin.
    cbn in CONV; inv CONV.
    cbn in *.
    unfold InterpreterStack64BitIntptr.LP.ITOP.int_to_ptr in ITP.
    break_match_hyp_inv.
    rewrite Integers.unsigned_repr.
    2: {
      unfold Integers.max_unsigned.
      lia.
    }
    auto.
  Qed.
End ItoP_Refine_InfFin.

Module Type LangRefine (IS1 : InterpreterStack) (IS2 : InterpreterStack) (AC1 : AddrConvert IS1.LP.ADDR IS1.LP.PTOI IS2.LP.ADDR IS2.LP.PTOI) (AC2 : AddrConvert IS2.LP.ADDR IS2.LP.PTOI IS1.LP.ADDR IS1.LP.PTOI) (LLVM1 : LLVMTopLevel IS1) (LLVM2 : LLVMTopLevel IS2) (TLR1 : TopLevelRefinements IS1 LLVM1) (TLR2 : TopLevelRefinements IS2 LLVM2) (IPS : IPConvertSafe IS2.LP.IP IS1.LP.IP) (ACS : AddrConvertSafe IS2.LP.ADDR IS2.LP.PTOI IS1.LP.ADDR IS1.LP.PTOI AC2 AC1) (DVC : DVConvert IS1.LP IS2.LP AC1 IS1.LP.Events IS2.LP.Events) (DVCrev : DVConvert IS2.LP IS1.LP AC2 IS2.LP.Events IS1.LP.Events) (EC : EventConvert IS1.LP IS2.LP AC1 AC2 IS1.LP.Events IS2.LP.Events DVC DVCrev) (TC : TreeConvert IS1 IS2 AC1 AC2 DVC DVCrev EC) (VMEM_IP_PROP1 : VMemInt_Intptr_Properties IS1.LP.IP) (VMEM_IP_PROP2 : VMemInt_Intptr_Properties IS2.LP.IP) (VMEM_REF : VMemInt_Refine IS1.LP.IP IS2.LP.IP) (SIZEOF_REF : Sizeof_Refine IS1.LP.SIZEOF IS2.LP.SIZEOF) (ITOP_REF : ItoP_Refine IS1 IS2 AC1 AC2).
  Import TLR2.

  Import TC.
  Import EC.
  Import DVC.
  Import IPS.
  Import ACS.
  Import SIZEOF_REF.
  Import ITOP_REF.

  Module DVCSafe := DVConvertSafe IS2.LP IS1.LP AC2 AC1 ACS IPS IS2.LP.Events IS1.LP.Events DVCrev DVC.
  Import DVCSafe.

  Module MBT := MemBytesTheory IS2.LP IS2.LLVM.MEM.MP ByteM IS2.LLVM.MEM.CP.
  Import MBT.

  (**  Converting state between the two languages *)

  (*
  Definition convert_global_env_lazy (g : IS1.LLVM.Global.global_env) : IS2.LLVM.Global.global_env
    := map (fun '(k, dv) => (k, dvalue_convert_lazy dv)) g.

  Definition convert_local_env_lazy (l : IS1.LLVM.Local.local_env) : IS2.LLVM.Local.local_env
    := map (fun '(k, uv) => (k, uvalue_convert_lazy uv)) l.
   *)

  Definition convert_global_env_strict (g : IS1.LLVM.Global.global_env) : OOM IS2.LLVM.Global.global_env
    := map_monad (fun '(k, dv) => dv' <- dvalue_convert_strict dv;;
                               ret (k, dv')) g.

  Definition convert_local_env_strict (l : IS1.LLVM.Local.local_env) : OOM IS2.LLVM.Local.local_env
    := map_monad (fun '(k, uv) => uv' <- uvalue_convert_strict uv;;
                               ret (k, uv')) l.

  (*
  Definition convert_stack_lazy (s : @stack IS1.LLVM.Local.local_env) : (@stack IS2.LLVM.Local.local_env)
    := map convert_local_env_lazy s.
   *)

  Definition convert_stack_strict (s : @stack IS1.LLVM.Local.local_env) : OOM (@stack IS2.LLVM.Local.local_env)
    := map_monad convert_local_env_strict s.

  (** Refinement between states *)
  (* Not sure if this is right...

     Presumably if [g1] OOMs when converted, we wouldn't have a [g2]
     anyway?
   *)
  (*
  Definition global_refine_lazy (g1 : IS1.LLVM.Global.global_env) (g2 : IS2.LLVM.Global.global_env) : Prop
    := alist_refine dvalue_refine_lazy g1 g2.

  Lemma global_refine_lazy_empty :
    global_refine_lazy [] [].
  Proof.
    apply alist_refine_empty.
  Qed.
   *)

  Definition global_refine_strict (g1 : IS1.LLVM.Global.global_env) (g2 : IS2.LLVM.Global.global_env) : Prop
    := alist_refine dvalue_refine_strict g1 g2.

  Lemma global_refine_strict_empty :
    global_refine_strict [] [].
  Proof.
    apply alist_refine_empty.
  Qed.

  Lemma global_refine_strict_add :
    forall rid genv1 genv2 dv1 dv2,
      global_refine_strict genv1 genv2 ->
      dvalue_refine_strict dv1 dv2 ->
      global_refine_strict (FMapAList.alist_add rid dv1 genv1) (FMapAList.alist_add rid dv2 genv2).
  Proof.
    intros rid genv1 genv2 dv1 dv2 H H0.
    eapply alist_refine_add with (x:=(rid, dv1)) (y:=(rid, dv2)); cbn; eauto.
  Qed.

  (*
  Definition local_refine_lazy (l1 : IS1.LLVM.Local.local_env) (l2 : IS2.LLVM.Local.local_env) : Prop
    := alist_refine uvalue_refine_lazy l1 l2.

  Lemma local_refine_lazy_empty :
    local_refine_lazy [] [].
  Proof.
    apply alist_refine_empty.
  Qed.
   *)

  Definition local_refine_strict (l1 : IS1.LLVM.Local.local_env) (l2 : IS2.LLVM.Local.local_env) : Prop
    := alist_refine uvalue_refine_strict l1 l2.

  Lemma local_refine_strict_empty :
    local_refine_strict [] [].
  Proof.
    apply alist_refine_empty.
  Qed.

  (*
  Definition stack_refine_lazy (s1 : @stack IS1.LLVM.Local.local_env) (s2 : @stack IS2.LLVM.Local.local_env) : Prop
    := Forall2 local_refine_lazy s1 s2.

  Lemma stack_refine_lazy_empty :
    stack_refine_lazy [] [].
  Proof.
    constructor.
  Qed.
   *)

  Definition stack_refine_strict (s1 : @stack IS1.LLVM.Local.local_env) (s2 : @stack IS2.LLVM.Local.local_env) : Prop
    := Forall2 local_refine_strict s1 s2.

  Lemma stack_refine_strict_empty :
    stack_refine_strict [] [].
  Proof.
    constructor.
  Qed.

  (*
  Definition local_stack_refine_lazy
    (ls1 : (IS1.LLVM.Local.local_env * @stack IS1.LLVM.Local.local_env)%type)
    (ls2 : (IS2.LLVM.Local.local_env * @stack IS2.LLVM.Local.local_env)%type)
    : Prop :=
    match ls1, ls2 with
    | (l1, s1), (l2, s2) =>
        local_refine_lazy l1 l2 /\ stack_refine_lazy s1 s2
    end.

  Lemma local_stack_refine_lazy_empty :
    local_stack_refine_lazy ([], []) ([], []).
  Proof.
    cbn.
    split.
    apply local_refine_lazy_empty.
    apply stack_refine_lazy_empty.
  Qed.
   *)

  Definition local_stack_refine_strict
    (ls1 : (IS1.LLVM.Local.local_env * @stack IS1.LLVM.Local.local_env)%type)
    (ls2 : (IS2.LLVM.Local.local_env * @stack IS2.LLVM.Local.local_env)%type)
    : Prop :=
    match ls1, ls2 with
    | (l1, s1), (l2, s2) =>
        local_refine_strict l1 l2 /\ stack_refine_strict s1 s2
    end.

  Lemma local_stack_refine_strict_empty :
    local_stack_refine_strict ([], []) ([], []).
  Proof.
    cbn.
    split.
    apply local_refine_strict_empty.
    apply stack_refine_strict_empty.
  Qed.

  (* TODO: move this *)
  Lemma local_stack_refine_strict_add :
    forall rid lenv1 lenv2 uv1 uv2,
      local_refine_strict lenv1 lenv2 ->
      uvalue_refine_strict uv1 uv2 ->
      local_refine_strict (FMapAList.alist_add rid uv1 lenv1) (FMapAList.alist_add rid uv2 lenv2).
  Proof.
    intros rid lenv1 lenv2 uv1 uv2 H H0.
    eapply alist_refine_add with (x:=(rid, uv1)) (y:=(rid, uv2)); cbn; eauto.
  Qed.

  (* TODO: move this *)
  Lemma stack_refine_strict_add :
    forall s1 s2 lenv1 lenv2,
      stack_refine_strict s1 s2 ->
      local_refine_strict lenv1 lenv2 ->
      stack_refine_strict (lenv1 :: s1) (lenv2 :: s2).
  Proof.
    intros s1 s2 lenv1 lenv2 H H0.
    red.
    apply Forall2_cons; auto.
  Qed.

  (** OOM Refinements *)
  Lemma Returns_ExternalCall_L0 :
    forall d f t args,
      @Returns E1.L0 E1.DV.dvalue d (trigger (E1.ExternalCall t f args)).
  Proof.
    intros d f t args.

    eapply ReturnsVis.
    unfold trigger.
    reflexivity.
    cbn.
    constructor.
    reflexivity.
  Qed.

  Opaque FinPROV.initial_provenance.
  Opaque InfPROV.initial_provenance.
  (* Opaque dvalue_convert_lazy. *)
  (* Opaque uvalue_convert_lazy. *)
  (* Opaque dvalue_refine_lazy. *)
  (* Opaque uvalue_refine_lazy. *)
  (* Opaque DVCrev.dvalue_convert_lazy. *)
  (* Opaque DVCrev.uvalue_convert_lazy. *)
  (* Opaque DVCrev.dvalue_refine_lazy. *)
  (* Opaque DVCrev.uvalue_refine_lazy. *)
  (* Opaque dvalue_convert_strict. *)
  (* Opaque uvalue_convert_strict. *)
  (* Opaque dvalue_refine_strict. *)
  (* Opaque uvalue_refine_strict. *)
  (* Opaque DVCrev.dvalue_convert_strict. *)
  (* Opaque DVCrev.uvalue_convert_strict. *)
  (* Opaque DVCrev.dvalue_refine_strict. *)
  (* Opaque DVCrev.uvalue_refine_strict. *)

  (** Model *)
  Import DynamicTypes TypToDtyp CFG.

  Definition event_refine_strict A B (e1 : IS1.LP.Events.L0 A) (e2 : IS2.LP.Events.L0 B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 (E1.ExternalCall dt1 f1 args1), inl1 (E2.ExternalCall dt2 f2 args2) =>
                _
            | inl1 (E1.IO_stdout msg1), inl1 (E2.IO_stdout msg2) =>
                _
            | inl1 (E1.IO_stderr msg1), inl1 (E2.IO_stderr msg2) =>
                _
            | inr1 (inl1 (E1.Intrinsic dt1 name1 args1)), inr1 (inl1 (E2.Intrinsic dt2 name2 args2)) =>
                _ (* IntrinsicE *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* Globals *)
            | inr1 (inr1 (inr1 (inl1 (inl1 e1)))), inr1 (inr1 (inr1 (inl1 (inl1 e2)))) =>
                _ (* Locals *)
            | inr1 (inr1 (inr1 (inl1 (inr1 e1)))), inr1 (inr1 (inr1 (inl1 (inr1 e2)))) =>
                _ (* Stack *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* External Calls *)
    { (* Doesn't say anything about return value... *)
      apply (dt1 = dt2 /\
               uvalue_refine_strict f1 f2 /\
               Forall2 dvalue_refine_strict args1 args2).
    }

    (* Stdout *)
    { apply (msg1 = msg2).
    }

    (* Stderr *)
    { apply (msg1 = msg2).
    }

    (* Intrinsics *)
    { apply (dt1 = dt2 /\
               name1 = name2 /\
               Forall2 dvalue_refine_strict args1 args2).
    }

    (* Globals *)
    { inversion e1.
      - (* Global write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_refine_strict dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0).
    }

    (* Locals *)
    { inversion e1.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_refine_strict dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0).
    }

    (* Stack *)
    { inversion e1.
      - (* Stack Push *)
        destruct e2 eqn:HE2.
        + apply (local_refine_strict args args0).
        + apply False.
      - (* Stack Pop *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply True.
    }

    (* MemoryE *)
    { inversion e1.
      - (* MemPush *)
        destruct e2 eqn:HE2.
        2-5: apply False.

        apply True.
      - (* MemPop *)
        destruct e2 eqn:HE2.
        2: apply True.
        all: apply False.
      - (* Alloca *)
        destruct e2 eqn:HE2.
        1,2,4,5: apply False.

        apply (t = t0 /\
                 num_elements = num_elements0 /\
                 align = align0).
      - (* Load *)
        destruct e2 eqn:HE2.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_refine_strict a a0).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_refine_strict a a0 /\
                 uvalue_refine_strict v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      - (* pickUnique *)
        subst.
        destruct e2.
        + apply (uvalue_refine_strict x x0).
        + exact False.
        + exact False.
      - (* pickNonPoison *)
        subst.
        destruct e2.
        + exact False.
        + apply (uvalue_refine_strict x x0).
        + exact False.
      - (* pick *)
        subst.
        destruct e2.
        + exact False.
        + exact False.
        + apply (uvalue_refine_strict x x0).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { destruct e1 as [e1_msg].
      destruct e2 as [e2_msg].
      exact (e1_msg = e2_msg).
    }

    (* FailureE *)
    { destruct e1 as [e1_msg].
      destruct e2 as [e2_msg].
      exact (e1_msg = e2_msg).
    }
  Defined.

  Definition L1_refine_strict A B (e1 : IS1.LP.Events.L1 A) (e2 : IS2.LP.Events.L1 B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 (E1.ExternalCall dt1 f1 args1), inl1 (E2.ExternalCall dt2 f2 args2) =>
                _
            | inl1 (E1.IO_stdout msg1), inl1 (E2.IO_stdout msg2) =>
                _
            | inl1 (E1.IO_stderr msg1), inl1 (E2.IO_stderr msg2) =>
                _
            | inr1 (inl1 (E1.Intrinsic dt1 name1 args1)), inr1 (inl1 (E2.Intrinsic dt2 name2 args2)) =>
                _ (* IntrinsicE *)
            | inr1 (inr1 (inl1 (inl1 e1))), inr1 (inr1 (inl1 (inl1 e2))) =>
                _ (* Locals *)
            | inr1 (inr1 (inl1 (inr1 e1))), inr1 (inr1 (inl1 (inr1 e2))) =>
                _ (* Stack *)
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2))))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* External Calls *)
    { (* Doesn't say anything about return value... *)
      apply (dt1 = dt2 /\
               uvalue_refine_strict f1 f2 /\
               Forall2 dvalue_refine_strict args1 args2).
    }

    (* Stdout *)
    { apply (msg1 = msg2).
    }

    (* Stderr *)
    { apply (msg1 = msg2).
    }

    (* Intrinsics *)
    { apply (dt1 = dt2 /\
               name1 = name2 /\
               Forall2 dvalue_refine_strict args1 args2).
    }

    (* Locals *)
    { inversion e1.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_refine_strict dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0).
    }

    (* Stack *)
    { inversion e1.
      - (* Stack Push *)
        destruct e2 eqn:HE2.
        + apply (local_refine_strict args args0).
        + apply False.
      - (* Stack Pop *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply True.
    }

    (* MemoryE *)
    { inversion e1.
      - (* MemPush *)
        destruct e2 eqn:HE2.
        2-5: apply False.

        apply True.
      - (* MemPop *)
        destruct e2 eqn:HE2.
        2: apply True.
        all: apply False.
      - (* Alloca *)
        destruct e2 eqn:HE2.
        1,2,4,5: apply False.

        apply (t = t0 /\
                 num_elements = num_elements0 /\
                 align = align0).
      - (* Load *)
        destruct e2 eqn:HE2.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_refine_strict a a0).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_refine_strict a a0 /\
                 uvalue_refine_strict v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      - (* pickUnique *)
        subst.
        destruct e2.
        + apply (uvalue_refine_strict x x0).
        + exact False.
        + exact False.
      - (* pickNonPoison *)
        subst.
        destruct e2.
        + exact False.
        + apply (uvalue_refine_strict x x0).
        + exact False.
      - (* pick *)
        subst.
        destruct e2.
        + exact False.
        + exact False.
        + apply (uvalue_refine_strict x x0).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { destruct e1 as [e1_msg].
      destruct e2 as [e2_msg].
      exact (e1_msg = e2_msg).
    }

    (* FailureE *)
    { destruct e1 as [e1_msg].
      destruct e2 as [e2_msg].
      exact (e1_msg = e2_msg).
    }
  Defined.

  Definition L2_refine_strict A B (e1 : IS1.LP.Events.L2 A) (e2 : IS2.LP.Events.L2 B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 (E1.ExternalCall dt1 f1 args1), inl1 (E2.ExternalCall dt2 f2 args2) =>
                _
            | inl1 (E1.IO_stdout msg1), inl1 (E2.IO_stdout msg2) =>
                _
            | inl1 (E1.IO_stderr msg1), inl1 (E2.IO_stderr msg2) =>
                _
            | inr1 (inl1 (E1.Intrinsic dt1 name1 args1)), inr1 (inl1 (E2.Intrinsic dt2 name2 args2)) =>
                _ (* IntrinsicE *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e0)))), inr1 (inr1 (inr1 (inr1 (inl1 e1)))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* External Calls *)
    { (* Doesn't say anything about return value... *)
      apply (dt1 = dt2 /\
               uvalue_refine_strict f1 f2 /\
               Forall2 dvalue_refine_strict args1 args2).
    }

    (* Stdout *)
    { apply (msg1 = msg2).
    }

    (* Stderr *)
    { apply (msg1 = msg2).
    }

    (* Intrinsics *)
    { apply (dt1 = dt2 /\
               name1 = name2 /\
               Forall2 dvalue_refine_strict args1 args2).
    }

    (* MemoryE *)
    { inversion e1.
      - (* MemPush *)
        destruct e2 eqn:HE2.
        2-5: apply False.

        apply True.
      - (* MemPop *)
        destruct e2 eqn:HE2.
        2: apply True.
        all: apply False.
      - (* Alloca *)
        destruct e2 eqn:HE2.
        1,2,4,5: apply False.

        apply (t = t0 /\
                 num_elements = num_elements0 /\
                 align = align0).
      - (* Load *)
        destruct e2 eqn:HE2.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_refine_strict a a0).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_refine_strict a a0 /\
                 uvalue_refine_strict v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      - (* pickUnique *)
        subst.
        destruct e2.
        + apply (uvalue_refine_strict x x0).
        + exact False.
        + exact False.
      - (* pickNonPoison *)
        subst.
        destruct e2.
        + exact False.
        + apply (uvalue_refine_strict x x0).
        + exact False.
      - (* pick *)
        subst.
        destruct e2.
        + exact False.
        + exact False.
        + apply (uvalue_refine_strict x x0).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { destruct e1 as [e1_msg].
      destruct e2 as [e2_msg].
      exact (e1_msg = e2_msg).
    }

    (* FailureE *)
    { destruct e1 as [e1_msg].
      destruct e2 as [e2_msg].
      exact (e1_msg = e2_msg).
    }
  Defined.

  Definition L3_refine_strict A B (e1 : IS1.LP.Events.L3 A) (e2 : IS2.LP.Events.L3 B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 (E1.ExternalCall dt1 f1 args1), inl1 (E2.ExternalCall dt2 f2 args2) =>
                _
            | inl1 (E1.IO_stdout msg1), inl1 (E2.IO_stdout msg2) =>
                _
            | inl1 (E1.IO_stderr msg1), inl1 (E2.IO_stderr msg2) =>
                _
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* PickE *)
            | inr1 (inr1 (inl1 e0)), inr1 (inr1 (inl1 e1)) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 e1)))), inr1 (inr1 (inr1 (inr1 (inr1 e2)))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* External Calls *)
    { (* Doesn't say anything about return value... *)
      apply (dt1 = dt2 /\
               uvalue_refine_strict f1 f2 /\
               Forall2 dvalue_refine_strict args1 args2).
    }

    (* Stdout *)
    { apply (msg1 = msg2).
    }

    (* Stderr *)
    { apply (msg1 = msg2).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      - (* pickUnique *)
        subst.
        destruct e2.
        + apply (uvalue_refine_strict x x0).
        + exact False.
        + exact False.
      - (* pickNonPoison *)
        subst.
        destruct e2.
        + exact False.
        + apply (uvalue_refine_strict x x0).
        + exact False.
      - (* pick *)
        subst.
        destruct e2.
        + exact False.
        + exact False.
        + apply (uvalue_refine_strict x x0).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { destruct e1 as [e1_msg].
      destruct e2 as [e2_msg].
      exact (e1_msg = e2_msg).
    }

    (* FailureE *)
    { destruct e1 as [e1_msg].
      destruct e2 as [e2_msg].
      exact (e1_msg = e2_msg).
    }
  Defined.

  Definition L4_refine_strict A B (e1 : IS1.LP.Events.L4 A) (e2 : IS2.LP.Events.L4 B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 (E1.ExternalCall dt1 f1 args1), inl1 (E2.ExternalCall dt2 f2 args2) =>
                _
            | inl1 (E1.IO_stdout msg1), inl1 (E2.IO_stdout msg2) =>
                _
            | inl1 (E1.IO_stderr msg1), inl1 (E2.IO_stderr msg2) =>
                _
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* OOME *)
            | inr1 (inr1 (inl1 e0)), inr1 (inr1 (inl1 e1)) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 e1))), inr1 (inr1 (inr1 (inr1 e2))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* External Calls *)
    { (* Doesn't say anything about return value... *)
      apply (dt1 = dt2 /\
               uvalue_refine_strict f1 f2 /\
               Forall2 dvalue_refine_strict args1 args2).
    }

    (* Stdout *)
    { apply (msg1 = msg2).
    }

    (* Stderr *)
    { apply (msg1 = msg2).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { destruct e1 as [e1_msg].
      destruct e2 as [e2_msg].
      exact (e1_msg = e2_msg).
    }

    (* FailureE *)
    { destruct e1 as [e1_msg].
      destruct e2 as [e2_msg].
      exact (e1_msg = e2_msg).
    }
  Defined.

  Definition event_res_refine_strict A B (e1 : IS1.LP.Events.L0 A) (res1 : A) (e2 : IS2.LP.Events.L0 B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                _
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* IntrinsicE *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* Globals *)
            | inr1 (inr1 (inr1 (inl1 (inl1 e1)))), inr1 (inr1 (inr1 (inl1 (inl1 e2)))) =>
                _ (* Locals *)
            | inr1 (inr1 (inr1 (inl1 (inr1 e1)))), inr1 (inr1 (inr1 (inl1 (inr1 e2)))) =>
                _ (* Stack *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* External Calls *)
    { inv e1.
      - (* ExternalCall *)
        inv e2.
        { apply (t = t0 /\
                 uvalue_refine_strict f f0 /\
                 Forall2 dvalue_refine_strict args args0 /\
                 dvalue_refine_strict res1 res2
                ).
        }
        all: exact False. (* Mismatch of event types *)
      - (* Stdout *)
        inv e2.
        2: {
          apply (str = str0).
        }
        all: exact False. (* Mismatch of event types *)
      - (* Stderr *)
        inv e2.
        3: {
          apply (str = str0).
        }
        all: exact False. (* Mismatch of event types *)
    }

    (* Intrinsics *)
    { inv e1.
      inv e2.
      apply (t = t0 /\
               f = f0 /\
               Forall2 dvalue_refine_strict args args0 /\
               dvalue_refine_strict res1 res2
            ).
    }

    (* Globals *)
    { inversion e1; subst.
      - (* Global write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_refine_strict dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                   dvalue_refine_strict res1 res2
                ).
    }

    (* Locals *)
    { inversion e1; subst.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_refine_strict dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                uvalue_refine_strict res1 res2).
    }

    (* Stack *)
    { inversion e1; subst.
      - (* Stack Push *)
        destruct e2 eqn:HE2.
        + apply (local_refine_strict args args0).
        + apply False.
      - (* Stack Pop *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply True.
    }

    (* MemoryE *)
    { inversion e1; subst.
      - (* MemPush *)
        destruct e2 eqn:HE2.
        2-5: apply False.

        apply True.
      - (* MemPop *)
        destruct e2 eqn:HE2.
        2: apply True.
        all: apply False.
      - (* Alloca *)
        destruct e2 eqn:HE2.
        1,2,4,5: apply False.

        apply (t = t0 /\
                 num_elements = num_elements0 /\
                 align = align0 /\
                 dvalue_refine_strict res1 res2).
      - (* Load *)
        destruct e2 eqn:HE2.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_refine_strict a a0 /\
                 uvalue_refine_strict res1 res2).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_refine_strict a a0 /\
                 uvalue_refine_strict v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      - (* pickUnique *)
        subst.
        destruct e2.
        + destruct res1 as [r1 P1].
          destruct res2 as [r2 P2].
          apply (uvalue_refine_strict x x0 /\ dvalue_refine_strict r1 r2).
        + exact False.
        + exact False.
      - (* pickNonPoison *)
        subst.
        destruct e2.
        + exact False.
        + destruct res1 as [r1 P1].
          destruct res2 as [r2 P2].
          apply (uvalue_refine_strict x x0 /\ dvalue_refine_strict r1 r2).
        + exact False.
      - (* pick *)
        subst.
        destruct e2.
        + exact False.
        + exact False.
        + destruct res1 as [r1 P1].
          destruct res2 as [r2 P2].
          apply (uvalue_refine_strict x x0 /\ dvalue_refine_strict r1 r2).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { destruct e1 as [e1_msg].
      destruct e2 as [e2_msg].
      exact (e1_msg = e2_msg).
    }

    (* FailureE *)
    { destruct e1 as [e1_msg].
      destruct e2 as [e2_msg].
      exact (e1_msg = e2_msg).
    }
  Defined.

  Definition L1_res_refine_strict A B (e1 : IS1.LP.Events.L1 A) (res1 : A) (e2 : IS2.LP.Events.L1 B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                _
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* IntrinsicE *)
            | inr1 (inr1 (inl1 (inl1 e1))), inr1 (inr1 (inl1 (inl1 e2))) =>
                _ (* Locals *)
            | inr1 (inr1 (inl1 (inr1 e1))), inr1 (inr1 (inl1 (inr1 e2))) =>
                _ (* Stack *)
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e0))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1))))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2))))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* External Calls *)
    { inv e1.
      - (* ExternalCall *)
        inv e2.
        { apply (t = t0 /\
                 uvalue_refine_strict f f0 /\
                 Forall2 dvalue_refine_strict args args0 /\
                 dvalue_refine_strict res1 res2
                ).
        }
        all: exact False. (* Mismatch of event types *)
      - (* Stdout *)
        inv e2.
        2: {
          apply (str = str0).
        }
        all: exact False. (* Mismatch of event types *)
      - (* Stderr *)
        inv e2.
        3: {
          apply (str = str0).
        }
        all: exact False. (* Mismatch of event types *)
    }

    (* Intrinsics *)
    { inv e1.
      inv e2.
      apply (t = t0 /\
               f = f0 /\
               Forall2 dvalue_refine_strict args args0 /\
               dvalue_refine_strict res1 res2
            ).
    }

    (* Locals *)
    { inversion e1; subst.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_refine_strict dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                uvalue_refine_strict res1 res2).
    }

    (* Stack *)
    { inversion e1; subst.
      - (* Stack Push *)
        destruct e2 eqn:HE2.
        + apply (local_refine_strict args args0).
        + apply False.
      - (* Stack Pop *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply True.
    }

    (* MemoryE *)
    { inversion e1; subst.
      - (* MemPush *)
        destruct e2 eqn:HE2.
        2-5: apply False.

        apply True.
      - (* MemPop *)
        destruct e2 eqn:HE2.
        2: apply True.
        all: apply False.
      - (* Alloca *)
        destruct e2 eqn:HE2.
        1,2,4,5: apply False.

        apply (t = t0 /\
                 num_elements = num_elements0 /\
                 align = align0 /\
                 dvalue_refine_strict res1 res2).
      - (* Load *)
        destruct e2 eqn:HE2.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_refine_strict a a0 /\
                 uvalue_refine_strict res1 res2).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_refine_strict a a0 /\
                 uvalue_refine_strict v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      - (* pickUnique *)
        subst.
        destruct e2.
        + destruct res1 as [r1 P1].
          destruct res2 as [r2 P2].
          apply (uvalue_refine_strict x x0 /\ dvalue_refine_strict r1 r2).
        + exact False.
        + exact False.
      - (* pickNonPoison *)
        subst.
        destruct e2.
        + exact False.
        + destruct res1 as [r1 P1].
          destruct res2 as [r2 P2].
          apply (uvalue_refine_strict x x0 /\ dvalue_refine_strict r1 r2).
        + exact False.
      - (* pick *)
        subst.
        destruct e2.
        + exact False.
        + exact False.
        + destruct res1 as [r1 P1].
          destruct res2 as [r2 P2].
          apply (uvalue_refine_strict x x0 /\ dvalue_refine_strict r1 r2).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { destruct e1 as [e1_msg].
      destruct e2 as [e2_msg].
      exact (e1_msg = e2_msg).
    }

    (* FailureE *)
    { destruct e1 as [e1_msg].
      destruct e2 as [e2_msg].
      exact (e1_msg = e2_msg).
    }
  Defined.

  Definition L2_res_refine_strict A B (e1 : IS1.LP.Events.L2 A) (res1 : A) (e2 : IS2.LP.Events.L2 B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                _
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* IntrinsicE *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e0)))), inr1 (inr1 (inr1 (inr1 (inl1 e1)))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* External Calls *)
    { inv e1.
      - (* ExternalCall *)
        inv e2.
        { apply (t = t0 /\
                 uvalue_refine_strict f f0 /\
                 Forall2 dvalue_refine_strict args args0 /\
                 dvalue_refine_strict res1 res2
                ).
        }
        all: exact False. (* Mismatch of event types *)
      - (* Stdout *)
        inv e2.
        2: {
          apply (str = str0).
        }
        all: exact False. (* Mismatch of event types *)
      - (* Stderr *)
        inv e2.
        3: {
          apply (str = str0).
        }
        all: exact False. (* Mismatch of event types *)
    }

    (* Intrinsics *)
    { inv e1.
      inv e2.
      apply (t = t0 /\
               f = f0 /\
               Forall2 dvalue_refine_strict args args0 /\
               dvalue_refine_strict res1 res2
            ).
    }

    (* MemoryE *)
    { inversion e1; subst.
      - (* MemPush *)
        destruct e2 eqn:HE2.
        2-5: apply False.

        apply True.
      - (* MemPop *)
        destruct e2 eqn:HE2.
        2: apply True.
        all: apply False.
      - (* Alloca *)
        destruct e2 eqn:HE2.
        1,2,4,5: apply False.

        apply (t = t0 /\
                 num_elements = num_elements0 /\
                 align = align0 /\
                 dvalue_refine_strict res1 res2).
      - (* Load *)
        destruct e2 eqn:HE2.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_refine_strict a a0 /\
                 uvalue_refine_strict res1 res2).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_refine_strict a a0 /\
                 uvalue_refine_strict v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      - (* pickUnique *)
        subst.
        destruct e2.
        + destruct res1 as [r1 P1].
          destruct res2 as [r2 P2].
          apply (uvalue_refine_strict x x0 /\ dvalue_refine_strict r1 r2).
        + exact False.
        + exact False.
      - (* pickNonPoison *)
        subst.
        destruct e2.
        + exact False.
        + destruct res1 as [r1 P1].
          destruct res2 as [r2 P2].
          apply (uvalue_refine_strict x x0 /\ dvalue_refine_strict r1 r2).
        + exact False.
      - (* pick *)
        subst.
        destruct e2.
        + exact False.
        + exact False.
        + destruct res1 as [r1 P1].
          destruct res2 as [r2 P2].
          apply (uvalue_refine_strict x x0 /\ dvalue_refine_strict r1 r2).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { destruct e1 as [e1_msg].
      destruct e2 as [e2_msg].
      exact (e1_msg = e2_msg).
    }

    (* FailureE *)
    { destruct e1 as [e1_msg].
      destruct e2 as [e2_msg].
      exact (e1_msg = e2_msg).
    }
  Defined.

  Definition L3_res_refine_strict A B (e1 : IS1.LP.Events.L3 A) (res1 : A) (e2 : IS2.LP.Events.L3 B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                _
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* PickE *)
            | inr1 (inr1 (inl1 e0)), inr1 (inr1 (inl1 e1)) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 e1)))), inr1 (inr1 (inr1 (inr1 (inr1 e2)))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* External Calls *)
    { inv e1.
      - (* ExternalCall *)
        inv e2.
        { apply (t = t0 /\
                 uvalue_refine_strict f f0 /\
                 Forall2 dvalue_refine_strict args args0 /\
                 dvalue_refine_strict res1 res2
                ).
        }
        all: exact False. (* Mismatch of event types *)
      - (* Stdout *)
        inv e2.
        2: {
          apply (str = str0).
        }
        all: exact False. (* Mismatch of event types *)
      - (* Stderr *)
        inv e2.
        3: {
          apply (str = str0).
        }
        all: exact False. (* Mismatch of event types *)
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      - (* pickUnique *)
        subst.
        destruct e2.
        + destruct res1 as [r1 P1].
          destruct res2 as [r2 P2].
          apply (uvalue_refine_strict x x0 /\ dvalue_refine_strict r1 r2).
        + exact False.
        + exact False.
      - (* pickNonPoison *)
        subst.
        destruct e2.
        + exact False.
        + destruct res1 as [r1 P1].
          destruct res2 as [r2 P2].
          apply (uvalue_refine_strict x x0 /\ dvalue_refine_strict r1 r2).
        + exact False.
      - (* pick *)
        subst.
        destruct e2.
        + exact False.
        + exact False.
        + destruct res1 as [r1 P1].
          destruct res2 as [r2 P2].
          apply (uvalue_refine_strict x x0 /\ dvalue_refine_strict r1 r2).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { destruct e1 as [e1_msg].
      destruct e2 as [e2_msg].
      exact (e1_msg = e2_msg).
    }

    (* FailureE *)
    { destruct e1 as [e1_msg].
      destruct e2 as [e2_msg].
      exact (e1_msg = e2_msg).
    }
  Defined.

  Definition L4_res_refine_strict A B (e1 : IS1.LP.Events.L4 A) (res1 : A) (e2 : IS2.LP.Events.L4 B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                _
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* OOME *)
            | inr1 (inr1 (inl1 e0)), inr1 (inr1 (inl1 e1)) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 e1))), inr1 (inr1 (inr1 (inr1 e2))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* External Calls *)
    { inv e1.
      - (* ExternalCall *)
        inv e2.
        { apply (t = t0 /\
                 uvalue_refine_strict f f0 /\
                 Forall2 dvalue_refine_strict args args0 /\
                 dvalue_refine_strict res1 res2
                ).
        }
        all: exact False. (* Mismatch of event types *)
      - (* Stdout *)
        inv e2.
        2: {
          apply (str = str0).
        }
        all: exact False. (* Mismatch of event types *)
      - (* Stderr *)
        inv e2.
        3: {
          apply (str = str0).
        }
        all: exact False. (* Mismatch of event types *)
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { destruct e1 as [e1_msg].
      destruct e2 as [e2_msg].
      exact (e1_msg = e2_msg).
    }

    (* FailureE *)
    { destruct e1 as [e1_msg].
      destruct e2 as [e2_msg].
      exact (e1_msg = e2_msg).
    }
  Defined.

  Definition call_refine_strict (A B : Type) (c1 : IS1.LP.Events.CallE A) (c2 : CallE B) : Prop.
  Proof.
    (* Calls *)
    { (* Doesn't say anything about return value... *)
      inv c1.
      inv c2.
      apply (t = t0 /\
               uvalue_refine_strict f f0 /\
               Forall2 uvalue_refine_strict args args0).
    }
  Defined.

  Definition call_res_refine_strict (A B : Type) (c1 : IS1.LP.Events.CallE A) (res1 : A) (c2 : CallE B) (res2 : B) : Prop.
  Proof.
    (* Calls *)
    { inv c1.
      inv c2.
      apply (t = t0 /\
               uvalue_refine_strict f f0 /\
               Forall2 uvalue_refine_strict args args0 /\
               uvalue_refine_strict res1 res2).
    }
  Defined.

  Definition L0'_refine_strict A B (e1 : IS1.LP.Events.L0' A) (e2 : IS2.LP.Events.L0' B) : Prop
    := (sum_prerel call_refine_strict event_refine_strict) _ _ e1 e2.

  Definition L0'_res_refine_strict A B (e1 : IS1.LP.Events.L0' A) (res1 : A) (e2 : IS2.LP.Events.L0' B) (res2 : B) : Prop
    := (sum_postrel call_res_refine_strict event_res_refine_strict) _ _ e1 res1 e2 res2.

  Definition exp_E_refine_strict A B (e1 : IS1.LP.Events.exp_E A) (e2 : IS2.LP.Events.exp_E B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                _ (* Globals *)
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* Locals *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* Globals *)
    { inversion e1.
      - (* Global write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_refine_strict dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0).
    }

    (* Locals *)
    { inversion e1.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_refine_strict dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0).
    }

    (* MemoryE *)
    { inversion e1.
      - (* MemPush *)
        destruct e2 eqn:HE2.
        2-5: apply False.

        apply True.
      - (* MemPop *)
        destruct e2 eqn:HE2.
        2: apply True.
        all: apply False.
      - (* Alloca *)
        destruct e2 eqn:HE2.
        1,2,4,5: apply False.

        apply (t = t0 /\
                 num_elements = num_elements0 /\
                 align = align0).
      - (* Load *)
        destruct e2 eqn:HE2.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_refine_strict a a0).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_refine_strict a a0 /\
                 uvalue_refine_strict v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      - (* pickUnique *)
        subst.
        destruct e2.
        + apply (uvalue_refine_strict x x0).
        + exact False.
        + exact False.
      - (* pickNonPoison *)
        subst.
        destruct e2.
        + exact False.
        + apply (uvalue_refine_strict x x0).
        + exact False.
      - (* pick *)
        subst.
        destruct e2.
        + exact False.
        + exact False.
        + apply (uvalue_refine_strict x x0).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { destruct e1 as [e1_msg].
      destruct e2 as [e2_msg].
      exact (e1_msg = e2_msg).
    }

    (* FailureE *)
    { destruct e1 as [e1_msg].
      destruct e2 as [e2_msg].
      exact (e1_msg = e2_msg).
    }
  Defined.

  Definition exp_E_res_refine_strict A B (e1 : IS1.LP.Events.exp_E A) (res1 : A) (e2 : IS2.LP.Events.exp_E B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                _ (* Globals *)
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                _ (* Locals *)
            | inr1 (inr1 (inl1 e1)), inr1 (inr1 (inl1 e2)) =>
                _ (* MemoryE *)
            | inr1 (inr1 (inr1 (inl1 e1))), inr1 (inr1 (inr1 (inl1 e2))) =>
                _ (* PickE *)
            | inr1 (inr1 (inr1 (inr1 (inl1 e1)))), inr1 (inr1 (inr1 (inr1 (inl1 e2)))) =>
                _ (* OOME *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1))))), inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2))))) =>
                _ (* UBE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 e2)))))) =>
                _ (* DebugE *)
            | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e1)))))), inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 e2)))))) =>
                _ (* FailureE *)
            | _, _ =>
                (* Mismatch of event types *)
                False
            end).

    (* Globals *)
    { inversion e1; subst.
      - (* Global write *)
        inversion e2; subst.
        + apply (id = id0 /\
                   dvalue_refine_strict dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                   dvalue_refine_strict res1 res2
                ).
    }

    (* Locals *)
    { inversion e1; subst.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_refine_strict dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                uvalue_refine_strict res1 res2).
    }

    (* MemoryE *)
    { inversion e1; subst.
      - (* MemPush *)
        destruct e2 eqn:HE2.
        2-5: apply False.

        apply True.
      - (* MemPop *)
        destruct e2 eqn:HE2.
        2: apply True.
        all: apply False.
      - (* Alloca *)
        destruct e2 eqn:HE2.
        1,2,4,5: apply False.

        apply (t = t0 /\
                 num_elements = num_elements0 /\
                 align = align0 /\
                 dvalue_refine_strict res1 res2).
      - (* Load *)
        destruct e2 eqn:HE2.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_refine_strict a a0 /\
                 uvalue_refine_strict res1 res2).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_refine_strict a a0 /\
                 uvalue_refine_strict v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      - (* pickUnique *)
        subst.
        destruct e2.
        + destruct res1 as [r1 P1].
          destruct res2 as [r2 P2].
          apply (uvalue_refine_strict x x0 /\ dvalue_refine_strict r1 r2).
        + exact False.
        + exact False.
      - (* pickNonPoison *)
        subst.
        destruct e2.
        + exact False.
        + destruct res1 as [r1 P1].
          destruct res2 as [r2 P2].
          apply (uvalue_refine_strict x x0 /\ dvalue_refine_strict r1 r2).
        + exact False.
      - (* pick *)
        subst.
        destruct e2.
        + exact False.
        + exact False.
        + destruct res1 as [r1 P1].
          destruct res2 as [r2 P2].
          apply (uvalue_refine_strict x x0 /\ dvalue_refine_strict r1 r2).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { destruct e1 as [e1_msg].
      destruct e2 as [e2_msg].
      exact (e1_msg = e2_msg).
    }

    (* FailureE *)
    { destruct e1 as [e1_msg].
      destruct e2 as [e2_msg].
      exact (e1_msg = e2_msg).
    }
  Defined.

  Definition instr_E_refine_strict A B (e1 : IS1.LP.Events.instr_E A) (e2 : IS2.LP.Events.instr_E B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                call_refine_strict _ _ e1 e2
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                (* Intrinsics *)
                _
            | inr1 (inr1 e1), inr1 (inr1 e2) =>
                exp_E_refine_strict _ _ e1 e2
            | _, _ =>
                False
            end).

    (* Intrinsics *)
    { inv e1.
      inv e2.
      apply (t = t0 /\
               f = f0 /\
               Forall2 dvalue_refine_strict args args0
            ).
    }
  Defined.

  Definition instr_E_res_refine_strict A B (e1 : IS1.LP.Events.instr_E A) (res1 : A) (e2 : IS2.LP.Events.instr_E B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                call_res_refine_strict _ _ e1 res1 e2 res2
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                (* Intrinsics *)
                _
            | inr1 (inr1 e1), inr1 (inr1 e2) =>
                exp_E_res_refine_strict _ _ e1 res1 e2 res2
            | _, _ =>
                False
            end).

    (* Intrinsics *)
    { inv e1.
      inv e2.
      apply (t = t0 /\
               f = f0 /\
               Forall2 dvalue_refine_strict args args0 /\
               dvalue_refine_strict res1 res2
            ).
    }
  Defined.

  Definition L0_E1E2_orutt_strict t1 t2
    : Prop :=
    orutt
      event_refine_strict
      event_res_refine_strict
      dvalue_refine_strict
      t1 t2 (OOM:=OOME).

  Definition L1_E1E2_orutt_strict t1 t2
    : Prop :=
    orutt
      L1_refine_strict
      L1_res_refine_strict
      (global_refine_strict × dvalue_refine_strict)
      t1 t2 (OOM:=OOME).

  Definition L2_E1E2_orutt_strict t1 t2
    : Prop :=
    orutt
      L2_refine_strict
      L2_res_refine_strict
      (local_refine_strict × stack_refine_strict × (global_refine_strict × dvalue_refine_strict))
      t1 t2 (OOM:=OOME).

  Definition model_E1E2_L0_orutt_strict p1 p2 :=
    L0_E1E2_orutt_strict
      (LLVM1.denote_vellvm (DTYPE_I 32%positive) "main" LLVM1.main_args (convert_types (mcfg_of_tle p1)))
      (LLVM2.denote_vellvm (DTYPE_I 32%positive) "main" LLVM2.main_args (convert_types (mcfg_of_tle p2))).

  Definition model_E1E2_L1_orutt_strict p1 p2 :=
    L1_E1E2_orutt_strict
      (LLVM1.model_oom_L1 p1)
      (LLVM2.model_oom_L1 p2).

  Definition model_E1E2_L2_orutt_strict p1 p2 :=
    L2_E1E2_orutt_strict
      (LLVM1.model_oom_L2 p1)
      (LLVM2.model_oom_L2 p2).

  Import TranslateFacts.
  Import RecursionFacts.

  (* TODO: Could be worth considering making sure this isn't behind a module? *)
  Lemma function_name_eq_equiv :
    forall id1 id2,
      LLVM1.function_name_eq id1 id2 = LLVM2.function_name_eq id1 id2.
  Proof.
    intros id1 id2.
    unfold LLVM1.function_name_eq, LLVM2.function_name_eq.
    reflexivity.
  Qed.

  Lemma trigger_alloca_E1E2_rutt_strict_sound :
    forall dt n osz,
      rutt event_refine_strict event_res_refine_strict dvalue_refine_strict
        (trigger (IS1.LP.Events.Alloca dt n osz)) (trigger (Alloca dt n osz)).
  Proof.
    intros dt n osz.
    apply rutt_trigger.
    - cbn. auto.
    - intros t1 t2 H.
      cbn in *.
      tauto.
  Qed.

  Lemma trigger_globalwrite_E1E2_rutt_strict_sound :
    forall gid r1 r2,
      dvalue_refine_strict r1 r2 ->
      rutt event_refine_strict event_res_refine_strict eq (trigger (GlobalWrite gid r1))
        (trigger (GlobalWrite gid r2)).
  Proof.
    intros gid r1 r2 H.
    apply rutt_trigger.
    - cbn. auto.
    - intros [] [] _.
      auto.
  Qed.

  Lemma allocate_declarations_E1E2_rutt_strict_sound :
    forall a,
      rutt event_refine_strict event_res_refine_strict eq (LLVM1.allocate_declaration a) (allocate_declaration a).
  Proof.
    intros a.
    induction a.
    unfold LLVM1.allocate_declaration, allocate_declaration.
    cbn.
    repeat setoid_rewrite function_name_eq_equiv.
    break_match.
    - apply rutt_Ret; reflexivity.
    - eapply rutt_bind with (RR:=dvalue_refine_strict).
      { apply trigger_alloca_E1E2_rutt_strict_sound.
      }

      intros r1 r2 H.
      apply trigger_globalwrite_E1E2_rutt_strict_sound.
      auto.
  Qed.

  Lemma allocate_one_E1E2_rutt_strict_sound :
    forall (m_declarations : list (LLVMAst.declaration dtyp))
      (m_definitions : list (LLVMAst.definition dtyp (cfg dtyp))),
      rutt event_refine_strict event_res_refine_strict eq
        (map_monad LLVM1.allocate_declaration (m_declarations ++ map LLVMAst.df_prototype m_definitions))
        (map_monad allocate_declaration (m_declarations ++ map LLVMAst.df_prototype m_definitions)).
  Proof.
    intros m_declarations m_definitions.
    remember (m_declarations ++ map LLVMAst.df_prototype m_definitions) as declarations.
    clear m_declarations m_definitions Heqdeclarations.
    induction declarations.
    - cbn.
      apply rutt_Ret.
      reflexivity.
    - cbn.
      eapply rutt_bind with (RR:=eq).
      { apply allocate_declarations_E1E2_rutt_strict_sound.
      }

      intros [] [] _.
      eapply rutt_bind with (RR:=eq); auto.

      intros r1 r2 R1R2.
      subst.
      apply rutt_Ret.
      reflexivity.
  Qed.

  Lemma allocate_global_E1E2_rutt_strict_sound :
    forall (m_globals : list (LLVMAst.global dtyp)),
      rutt event_refine_strict event_res_refine_strict eq
        (map_monad LLVM1.allocate_global m_globals)
        (map_monad allocate_global m_globals).
  Proof.
    intros m_globals.
    induction m_globals.
    - cbn; apply rutt_Ret; reflexivity.
    - cbn.
      eapply rutt_bind with (RR:=eq).
      { eapply rutt_bind with (RR:=dvalue_refine_strict).
        { apply trigger_alloca_E1E2_rutt_strict_sound.
        }

        intros r1 r2 H.
        apply trigger_globalwrite_E1E2_rutt_strict_sound; auto.
      }

      intros [] [] _.
      eapply rutt_bind with (RR:=eq); auto.

      intros r1 r2 R1R2.
      subst.
      apply rutt_Ret.
      reflexivity.
  Qed.

  Lemma exp_E_refine_strict_event_refine_strict :
    forall A B (e1 : IS1.LP.Events.exp_E A) (e2 : exp_E B),
      exp_E_refine_strict A B e1 e2 ->
      event_refine_strict A B (IS1.LP.Events.exp_to_L0 e1) (exp_to_L0 e2).
  Proof.
    intros A B e1 e2 H.
    destruct e1, e2.
    2,3: (cbn in H;
          (repeat break_match_hyp; try contradiction)).

    - destruct l, l0.
      2,3: (cbn in H;
            (repeat break_match_hyp; try contradiction)).

      all: cbn in *; auto.
    - destruct s, s0.
      2,3: (cbn in H;
            (repeat break_match_hyp; try contradiction)).

      + destruct l, l0.
        2,3: (cbn in H;
              (repeat break_match_hyp; try contradiction)).

        all: cbn in *; auto.

      + destruct s, s0.
        2,3: (cbn in H;
              (repeat break_match_hyp; try contradiction)).

        { destruct m, m0; cbn; auto.
        }

        { destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct p, p0; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct o, o0; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct u, u0; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct d, d0; cbn; auto. }
          { destruct f, f0; cbn; auto. }

        }
  Qed.

  Lemma exp_E_refine_strict_instr_E_refine_strict :
    forall A B (e1 : IS1.LP.Events.exp_E A) (e2 : exp_E B),
      exp_E_refine_strict A B e1 e2 ->
      instr_E_refine_strict A B (IS1.LP.Events.exp_to_instr e1) (exp_to_instr e2).
  Proof.
    intros A B e1 e2 H.
    destruct e1, e2.
    2,3: (cbn in H;
          (repeat break_match_hyp; try contradiction)).

    - destruct l, l0.
      2,3: (cbn in H;
            (repeat break_match_hyp; try contradiction)).

      all: cbn in *; auto.
    - destruct s, s0.
      2,3: (cbn in H;
            (repeat break_match_hyp; try contradiction)).

      + destruct l, l0.
        2,3: (cbn in H;
              (repeat break_match_hyp; try contradiction)).

        all: cbn in *; auto.

      + destruct s, s0.
        2,3: (cbn in H;
              (repeat break_match_hyp; try contradiction)).

        { destruct m, m0; cbn; auto.
        }

        { destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct p, p0; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct o, o0; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct u, u0; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct d, d0; cbn; auto. }
          { destruct f, f0; cbn; auto. }

        }
  Qed.

  Lemma instr_E_refine_strict_L0'_refine_strict :
    forall A B (e1 : IS1.LP.Events.instr_E A) (e2 : instr_E B),
      instr_E_refine_strict A B e1 e2 ->
      L0'_refine_strict A B (IS1.LP.Events.instr_to_L0' e1) (instr_to_L0' e2).
  Proof.
    intros A B e1 e2 H.
    unfold L0'_refine_strict.
    destruct e1, e2.
    2,3: (cbn in H;
          (repeat break_match_hyp; try contradiction)).

    - destruct c, c0.
      cbn in *.
      constructor; cbn.
      tauto.
    - destruct s, s0.
      2,3: (cbn in H;
            (repeat break_match_hyp; try contradiction)).

      + destruct i, i0.
        cbn in *.
        constructor; cbn.
        tauto.

      + destruct e, e0.
        2,3: (cbn in H;
              (repeat break_match_hyp; try contradiction)).

        { destruct l, l0; cbn; constructor; cbn; auto.
        }

        { destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct l, l0; cbn; constructor; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct m, m0; cbn; constructor; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct p, p0; cbn; constructor; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct o, o0; cbn; constructor; cbn; auto. }
          { destruct s, s0; cbn; constructor; auto.
            destruct s, s0; try solve [ cbn in H; contradiction ].
            - (* Debug *)
              destruct d, d0; cbn in *; auto.
            - (* Failure *)
              destruct f, f0.
              cbn in *; auto.
          }
        }
  Qed.

  Lemma event_refine_strict_exp_E_refine_strict_inv :
    forall A B (e1 : IS1.LP.Events.exp_E A) (e2 : exp_E B) a b,
      event_res_refine_strict A B (IS1.LP.Events.exp_to_L0 e1) a (exp_to_L0 e2) b ->
      exp_E_refine_strict A B e1 e2.
  Proof.
    intros A B e1 e2 a b H.
    destruct e1, e2.
    2-3: (cbn in *;
          break_match_hyp; subst; cbn in *; auto).

    2: {
      repeat (break_match_hyp; subst; cbn in *; auto).
      all: inv Heql0.
    }

    - destruct l, l0.
      2,3: (cbn in H;
            (repeat break_match_hyp; try contradiction)).

      all: cbn in *; tauto.
    - destruct s, s0.
      2,3: (cbn in H;
            (repeat break_match_hyp; try contradiction)).

      + destruct l, l0.
        2,3: (cbn in H;
              (repeat break_match_hyp; try contradiction)).

        all: cbn in *; tauto.

      + destruct s, s0.
        2,3: (cbn in H;
              (repeat break_match_hyp; try contradiction)).

        { destruct m, m0; cbn in *; tauto.
        }

        { destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct p, p0; cbn in *; auto;
            destruct a, b;
            tauto.
          }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct o, o0; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct u, u0; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct d, d0; cbn; auto. }
          { destruct f, f0; cbn; auto. }

        }
  Qed.

  Lemma event_res_refine_strict_exp_E_res_refine_strict_inv :
    forall A B (e1 : IS1.LP.Events.exp_E A) (e2 : exp_E B) a b,
      event_res_refine_strict A B (IS1.LP.Events.exp_to_L0 e1) a (exp_to_L0 e2) b ->
      exp_E_res_refine_strict A B e1 a e2 b.
  Proof.
    intros A B e1 e2 a b H.
    destruct e1, e2.
    2-3: (cbn in *;
          break_match_hyp; subst; cbn in *; auto).

    2: {
      repeat (break_match_hyp; subst; cbn in *; auto).
      all: inv Heql0.
    }

    - destruct l, l0.
      2,3: (cbn in H;
            (repeat break_match_hyp; try contradiction)).

      all: cbn in *; tauto.
    - destruct s, s0.
      2,3: (cbn in H;
            (repeat break_match_hyp; try contradiction)).

      + destruct l, l0.
        2,3: (cbn in H;
              (repeat break_match_hyp; try contradiction)).

        all: cbn in *; tauto.

      + destruct s, s0.
        2,3: (cbn in H;
              (repeat break_match_hyp; try contradiction)).

        { destruct m, m0; cbn in *; tauto.
        }

        { destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct p, p0; cbn in *; auto.
          }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct o, o0; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct u, u0; cbn; auto. }

          destruct s, s0.
          2,3: (cbn in H;
                (repeat break_match_hyp; try contradiction)).

          { destruct d, d0; cbn; auto. }
          { destruct f, f0; cbn; auto. }

        }
  Qed.

  Lemma L0'_res_refine_strict_instr_E_res_refine_strict_inv :
    forall A B (e1 : IS1.LP.Events.instr_E A) (e2 : instr_E B) a b,
      L0'_res_refine_strict A B (IS1.LP.Events.instr_to_L0' e1) a (instr_to_L0' e2) b ->
      instr_E_res_refine_strict A B e1 a e2 b.
  Proof.
    intros A B e1 e2 a b H.
    destruct e1, e2.
    1-3:
      (cbn in *;
       repeat (first [ tauto
                     | break_match_hyp; subst; cbn in *; auto
                     | repeat match goal with
                         | H: L0'_res_refine_strict _ _ _ _ _ _ |- _ =>
                             inv H; subst_existT; unfold call_res_refine_strict in *; cbn in *
                         end
                 ]
         )).

    - destruct s, s0.
      1-3:
        (cbn in *;
         repeat (first [ tauto
                       | break_match_hyp; subst; cbn in *; auto
                       | repeat match goal with
                           | H: L0'_res_refine_strict _ _ _ _ _ _ |- _ =>
                               inv H; subst_existT; unfold call_res_refine_strict in *; cbn in *
                           end
                   ]
        )).

      destruct e, e0.
      1-3:
        (cbn in *;
         repeat (first [ tauto
                       | break_match_hyp; subst; cbn in *; auto
                       | repeat match goal with
                           | H: L0'_res_refine_strict _ _ _ _ _ _ |- _ =>
                               inv H; subst_existT; unfold call_res_refine_strict in *; cbn in *
                           end
                   ]
        )).

      + destruct s;
          (cbn in *;
           repeat (first [ tauto
                         | break_match_hyp; subst; cbn in *; auto
                         | repeat match goal with
                             | H: L0'_res_refine_strict _ _ _ _ _ _ |- _ =>
                                 inv H; subst_existT; unfold call_res_refine_strict in *; cbn in *
                             end
                     ]
          )).
  Qed.

  Lemma translate_exp_to_L0_E1E2_rutt :
    forall {R1 R2} {RR : R1 -> R2 -> Prop} t1 t2,
      rutt exp_E_refine_strict exp_E_res_refine_strict RR
        t1
        t2 ->
      rutt event_refine_strict event_res_refine_strict RR
        (translate IS1.LP.Events.exp_to_L0 t1)
        (translate exp_to_L0 t2).
  Proof.
    intros *.
    revert t1 t2.
    ginit.
    gcofix CIH.
    intros * RUTT.
    rewrite !unfold_translate. punfold RUTT. red in RUTT.
    induction RUTT; intros; subst; simpl; pclearbot.
    - gstep.
      constructor.
      auto.
    - gstep.
      red.
      constructor.
      gbase.
      apply CIH.
      auto.
    - gstep; eauto.
      red.
      constructor; eauto.
      apply exp_E_refine_strict_event_refine_strict; auto.

      intros a b H1.

      gbase.
      apply CIH.

      apply event_res_refine_strict_exp_E_res_refine_strict_inv in H1.
      apply H0 in H1.
      pclearbot.
      pfold. red.
      punfold H1.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
  Qed.

  Lemma translate_exp_to_L0_E1E2_orutt :
    forall {R1 R2} {RR : R1 -> R2 -> Prop} t1 t2,
      orutt exp_E_refine_strict exp_E_res_refine_strict RR
        t1
        t2
        (OOM:=OOME) ->
      orutt event_refine_strict event_res_refine_strict RR
        (translate IS1.LP.Events.exp_to_L0 t1)
        (translate exp_to_L0 t2)
        (OOM:=OOME).
  Proof.
    intros *.
    revert t1 t2.
    ginit.
    gcofix CIH.
    intros * RUTT.
    rewrite !unfold_translate. punfold RUTT. red in RUTT.
    induction RUTT; intros; subst; simpl; pclearbot.
    - gstep.
      constructor.
      auto.
    - gstep.
      red.
      constructor.
      gbase.
      apply CIH.
      auto.
    - gstep; eauto.
      red.
      constructor; eauto.
      apply exp_E_refine_strict_event_refine_strict; auto.

      intros a b H2.

      gbase.
      apply CIH.

      apply event_res_refine_strict_exp_E_res_refine_strict_inv in H2.
      apply H0 in H2.
      pclearbot.
      pfold. red.
      punfold H2.
      intros o CONTRA.
      specialize (H1 o).
      apply H1.
      destruct e2; inv CONTRA.
      destruct s; inv H3.
      reflexivity.
    - gstep; eauto.
      red.
      cbn.
      change (inr1 (inr1 (inr1 (inr1 (resum IFun A e))))) with (@subevent _ _ (ReSum_inr IFun sum1 OOME
                                                                               (IntrinsicE +'
                                                                                              LLVMGEnvE +' (LLVMEnvE +' LLVMStackE) +' MemoryE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE)
                                                                               ExternalCallE) A e).
      apply EqVisOOM.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
  Qed.

  Lemma instr_E_res_refine_strict_exp_E_res_refine_strict_inv :
    forall A B (e1 : IS1.LP.Events.exp_E A) (e2 : exp_E B) a b,
      instr_E_res_refine_strict A B (IS1.LP.Events.exp_to_instr e1) a (exp_to_instr e2) b ->
      exp_E_res_refine_strict A B e1 a e2 b.
  Proof.
    intros A B e1 e2 a b H.
    destruct e1, e2.
    1-3:(cbn in *;
       repeat (first [ tauto
                     | break_match_hyp; subst; cbn in *; auto
                     | repeat match goal with
                         | H: instr_E_res_refine_strict _ _ _ _ _ _ |- _ =>
                             inv H; subst_existT; unfold call_res_refine_strict in *; cbn in *
                         end
                 ]
         )).

    - destruct s, s0.
      1-3:
        (cbn in *;
         repeat (first [ tauto
                       | break_match_hyp; subst; cbn in *; auto
                       | repeat match goal with
                           | H: instr_E_res_refine_strict _ _ _ _ _ _ |- _ =>
                               inv H; subst_existT; unfold call_res_refine_strict in *; cbn in *
                           end
                   ]
        )).

      destruct s, s0.
      1-3:
        (cbn in *;
         repeat (first [ tauto
                       | break_match_hyp; subst; cbn in *; auto
                       | repeat match goal with
                           | H: L0'_res_refine_strict _ _ _ _ _ _ |- _ =>
                               inv H; subst_existT; unfold call_res_refine_strict in *; cbn in *
                           end
                   ]
        )).

      + destruct s;
          (cbn in *;
           repeat (first [ tauto
                         | break_match_hyp; subst; cbn in *; auto
                         | repeat match goal with
                             | H: L0'_res_refine_strict _ _ _ _ _ _ |- _ =>
                                 inv H; subst_existT; unfold call_res_refine_strict in *; cbn in *
                             end
                     ]
          )).
  Qed.

  Lemma translate_instr_to_L0'_E1E2_rutt_strict :
    forall {R1 R2} {RR : R1 -> R2 -> Prop} t1 t2,
      rutt instr_E_refine_strict instr_E_res_refine_strict RR t1 t2 ->
      rutt L0'_refine_strict L0'_res_refine_strict RR
        (translate IS1.LP.Events.instr_to_L0' t1)
        (translate instr_to_L0' t2).
  Proof.
    intros *.
    revert t1 t2.
    ginit.
    gcofix CIH.
    intros * RUTT.
    rewrite !unfold_translate. punfold RUTT. red in RUTT.
    induction RUTT; intros; subst; simpl; pclearbot.
    - gstep.
      constructor.
      auto.
    - gstep.
      red.
      constructor.
      gbase.
      apply CIH.
      auto.
    - gstep; eauto.
      red.
      constructor; eauto.
      apply instr_E_refine_strict_L0'_refine_strict; auto.

      intros a b H2.

      gbase.
      apply CIH.

      apply L0'_res_refine_strict_instr_E_res_refine_strict_inv in H2.
      apply H0 in H2.
      pclearbot.
      pfold. red.
      punfold H2.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
  Qed.

  Lemma translate_instr_to_L0'_E1E2_orutt_strict :
    forall {R1 R2} {RR : R1 -> R2 -> Prop} t1 t2,
      orutt instr_E_refine_strict instr_E_res_refine_strict RR t1 t2 (OOM:=OOME) ->
      orutt L0'_refine_strict L0'_res_refine_strict RR
        (translate IS1.LP.Events.instr_to_L0' t1)
        (translate instr_to_L0' t2)
        (OOM:=OOME).
  Proof.
    intros *.
    revert t1 t2.
    ginit.
    gcofix CIH.
    intros * RUTT.
    rewrite !unfold_translate. punfold RUTT. red in RUTT.
    induction RUTT; intros; subst; simpl; pclearbot.
    - gstep.
      constructor.
      auto.
    - gstep.
      red.
      constructor.
      gbase.
      apply CIH.
      auto.
    - gstep; eauto.
      red.
      constructor; eauto.
      apply instr_E_refine_strict_L0'_refine_strict; auto.

      intros a b H2.

      gbase.
      apply CIH.

      apply L0'_res_refine_strict_instr_E_res_refine_strict_inv in H2.
      apply H0 in H2.
      pclearbot.
      pfold. red.
      punfold H2.

      intros o CONTRA.
      eapply H1.
      destruct e2.
      unfold instr_to_L0' in CONTRA.
      inv CONTRA.
      cbn in *; break_match_hyp; inv CONTRA.
      cbn in *; break_match_hyp; inv H3.
      cbn in *; break_match_hyp; inv H4.
      reflexivity.
    - gstep; eauto.
      red.
      cbn.
      unfold exp_to_instr.
      unfold subevent.
      change (inr1 (inr1 (inr1 (inr1 (inr1 (resum IFun A e)))))) with
        (@subevent _ _ (ReSum_inr IFun sum1 OOME
                          (ExternalCallE +' IntrinsicE +' LLVMGEnvE +' (LLVMEnvE +' LLVMStackE) +' MemoryE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE)
                          CallE) A e).
      apply EqVisOOM.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
  Qed.

  Lemma translate_exp_to_instr_E1E2_rutt_strict :
    forall {R1 R2} {RR : R1 -> R2 -> Prop} t1 t2,
      rutt exp_E_refine_strict exp_E_res_refine_strict RR t1 t2 ->
      rutt instr_E_refine_strict instr_E_res_refine_strict RR
        (translate IS1.LP.Events.exp_to_instr t1)
        (translate exp_to_instr t2).
  Proof.
    intros *.
    revert t1 t2.
    ginit.
    gcofix CIH.
    intros * RUTT.
    rewrite !unfold_translate. punfold RUTT. red in RUTT.
    induction RUTT; intros; subst; simpl; pclearbot.
    - gstep.
      constructor.
      auto.
    - gstep.
      red.
      constructor.
      gbase.
      apply CIH.
      auto.
    - gstep; eauto.
      red.
      cbn.
      constructor; eauto.
      intros a b H2.

      gbase.
      apply CIH.

      apply instr_E_res_refine_strict_exp_E_res_refine_strict_inv in H2.
      apply H0 in H2.
      pclearbot.
      pfold. red.
      punfold H2.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
  Qed.

  Lemma translate_exp_to_instr_E1E2_orutt_strict :
    forall {R1 R2} {RR : R1 -> R2 -> Prop} t1 t2,
      orutt exp_E_refine_strict exp_E_res_refine_strict RR t1 t2 (OOM:=OOME) ->
      orutt instr_E_refine_strict instr_E_res_refine_strict RR
        (translate IS1.LP.Events.exp_to_instr t1)
        (translate exp_to_instr t2)
        (OOM:=OOME).
  Proof.
    intros *.
    revert t1 t2.
    ginit.
    gcofix CIH.
    intros * RUTT.
    rewrite !unfold_translate. punfold RUTT. red in RUTT.
    induction RUTT; intros; subst; simpl; pclearbot.
    - gstep.
      constructor.
      auto.
    - gstep.
      red.
      constructor.
      gbase.
      apply CIH.
      auto.
    - gstep; eauto.
      red.
      cbn.
      constructor; eauto.
      intros a b H2.

      gbase.
      apply CIH.

      apply instr_E_res_refine_strict_exp_E_res_refine_strict_inv in H2.
      apply H0 in H2.
      pclearbot.
      pfold. red.
      punfold H2.

      intros o CONTRA.
      eapply H1.
      inv CONTRA.
      reflexivity.
    - gstep; eauto.
      red.
      cbn.
      unfold exp_to_instr.
      unfold subevent.
      change (inr1 (inr1 (resum IFun A e))) with
        (@subevent _ _ (ReSum_inr IFun sum1 OOME
                          (IntrinsicE +' exp_E)
                          CallE) A e).
      apply EqVisOOM.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
    - rewrite tau_euttge, unfold_translate. eauto with itree.
  Qed.

  Lemma translate_LU_to_exp_lookup_id_orutt :
    forall id : LLVMAst.ident,
      orutt exp_E_refine_strict exp_E_res_refine_strict uvalue_refine_strict
        (translate IS1.LP.Events.LU_to_exp (IS1.LLVM.D.lookup_id id)) (translate LU_to_exp (lookup_id id))
        (OOM:=OOME).
  Proof.
    intros id.
    destruct id.
    - cbn.
      repeat rewrite translate_bind.
      repeat rewrite translate_trigger.
      repeat setoid_rewrite translate_ret.

      repeat rewrite bind_trigger.
      apply orutt_Vis;
        [cbn; auto| |].

      intros * ?.
      apply orutt_Ret.
      cbn in H.
      apply dvalue_refine_strict_dvalue_to_uvalue.
      destruct H.
      auto.

      intros o CONTRA.
      dependent destruction CONTRA.
    - cbn.
      repeat rewrite translate_bind.
      repeat rewrite translate_trigger.
      repeat setoid_rewrite translate_ret.

      repeat rewrite bind_trigger.
      apply orutt_Vis;
        [cbn; auto| |].

      intros * ?.
      apply orutt_Ret.
      destruct H.
      auto.

      intros o CONTRA.
      dependent destruction CONTRA.
  Qed.

  (* TODO: move this ltac, and probably use more *)
  Ltac rewrite_uvalue_convert_strict :=
    repeat
      match goal with
      | H: uvalue_convert_strict _ = _ |- _ =>
          rewrite H; clear H
      end.


  Ltac solve_pick_uvalue_orutt :=
    apply orutt_trigger; cbn;
    [ cbn;
      unfold uvalue_refine_strict; cbn;
      repeat rewrite_uvalue_convert_strict; auto
    | intros [t1] [t2] [REF1 REF2];
      cbn; auto
    | intros o CONTRA;
      inv CONTRA
    ].


  Lemma is_concrete_l:
    forall (l : list DV1.uvalue) (l' : list DV2.uvalue),
      Forall2 (fun (a : DV1.uvalue) (b : DV2.uvalue) => uvalue_convert_strict a = NoOom b) l l' ->
      forallb IS1.LP.Events.DV.is_concrete l = true ->
      forallb is_concrete l' = true.
  Proof.
    intros l l' H.
    induction H; intros HL.
    - reflexivity.
    - cbn in *.
      apply andb_prop in HL.
      destruct HL as [HX HL].
      specialize (uvalue_refine_strict_preserves_is_concrete x y _ H HX) as HY.
      rewrite HY. clear H HX HY.
      rewrite IHForall2; auto.
  Qed.


  Lemma is_concrete_l_false:
    forall (fields : list DV1.uvalue) (l : list DV2.uvalue),
      Forall2 (fun (a : DV1.uvalue) (b : DV2.uvalue) => uvalue_convert_strict a = NoOom b) fields l ->
      forallb IS1.LP.Events.DV.is_concrete fields = false ->
      forallb is_concrete l = true
      -> False.
  Proof.
    intros fields l H.
    induction H; intros HF HL.
    - inversion HF.
    - simpl in *.
      apply Bool.andb_false_elim in HF.
      apply andb_prop in HL.
      destruct HL as [HY HL].
      destruct HF as [HF | HF].
      + rewrite (uvalue_refine_strict_preserves_is_concrete _ _ false H HF) in HY.
        inversion HY.
      + eapply IHForall2; eauto.
  Qed.

  (* SAZ: This could be significantly generalized. *)
  Lemma map_dvalue_convert_strict_succeeds:
    forall (fields : list DV1.uvalue) (l : list DV2.uvalue),
      Forall2 (fun (a : DV1.uvalue) (b : DV2.uvalue) => uvalue_convert_strict a = NoOom b) fields l ->
      forall l0 : list IS1.LP.Events.DV.dvalue,
        Forall2
          (fun (a : IS1.LP.Events.DV.uvalue) (b : IS1.LP.Events.DV.dvalue) =>
             IS1.LP.Events.DV.uvalue_to_dvalue a = inr b) fields l0 ->
        forall l1 : list dvalue,
          map_monad uvalue_to_dvalue l = inr l1 -> map_monad dvalue_convert_strict l0 = NoOom l1.
  Proof.
    intros fields l Heqo l0 Heqs l1 Heqs0.
    rewrite map_monad_err_Forall2 in Heqs0.
    rewrite map_monad_oom_Forall2.
    revert l0 Heqs l1 Heqs0.
    induction Heqo; intros; inversion Heqs; inversion Heqs0; subst.
    - constructor.
    - constructor; eauto.
      clear Heqo IHHeqo Heqs Heqs0 H4 H9 l l' l'0 l'1.
      destruct (uvalue_to_dvalue_dvalue_refine_strict _ _ _ H H2) as [z [HZ HRZ]].
      unfold dvalue_refine_strict in HRZ.
      rewrite H7 in HZ. inversion HZ.
      auto.
  Qed.


  (* TODO: Should I move this out of LangRefine and into some kind of
     utility module based on DvalueConversions.v? *)
  Lemma pick_your_poison_orutt :
    forall r1 r2,
      uvalue_refine_strict r1 r2 ->
      orutt exp_E_refine_strict exp_E_res_refine_strict
        dvalue_refine_strict (IS1.LLVM.D.pick_your_poison r1)
        (pick_your_poison r2)
        (OOM:=OOME).
  Proof.
    intros r1.
    unfold pick_your_poison, IS1.LLVM.D.pick_your_poison.
    destruct r1; intros r2 HRS;
    rewrite uvalue_refine_strict_equation in HRS; cbn in HRS;
      try solve
        [
          inv HRS; cbn;
          apply orutt_Ret;
          rewrite dvalue_refine_strict_equation; cbn; auto
        | break_match_hyp_inv;
          cbn;
          apply orutt_Ret;
          rewrite dvalue_refine_strict_equation;
          cbn;
          rewrite Heqo;
          reflexivity
        | repeat break_match_hyp_inv;
          cbn in *;
          eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2));
            cbn;
          [ solve_pick_uvalue_orutt
          | intros [?r1] [?r2] ?H0;
            cbn in *;
            apply orutt_Ret; auto
          ]
        ].
    - (* Poison *)
      inv HRS; cbn.
      eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)); eauto.
      { (* pick_uvalue *)
        apply orutt_trigger; cbn.
        unfold uvalue_refine_strict; cbn; reflexivity.
        intros [t1] [t2] [REF1 REF2].
        cbn; auto.
        intros o CONTRA.
        inv CONTRA.
      }

      intros r1 r2 H.
      destruct r1, r2.
      cbn in *.
      apply orutt_Ret; auto.

    - (* Undef *)
      inv HRS; cbn.
      eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)); eauto.
      { (* pick_uvalue *)
        apply orutt_trigger; cbn.
        unfold uvalue_refine_strict; cbn; reflexivity.
        intros [t1] [t2] [REF1 REF2].
        cbn; auto.
        intros o CONTRA.
        inv CONTRA.
      }

      intros r1 r2 H.
      destruct r1, r2.
      cbn in *.
      apply orutt_Ret; auto.

    - (* Structs *)
      break_match_hyp; inv HRS; cbn.
      rewrite map_monad_oom_Forall2 in Heqo.
      unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick.
      cbn.
      break_match_goal.
      + specialize (is_concrete_l fields l Heqo Heqb) as HL.
        rewrite HL.
        clear Heqb HL.
        break_match_goal.
        * assert (exists v, map_monad uvalue_to_dvalue l = inl v).
          { revert s Heqs.
            induction Heqo; intros; [inversion Heqs|].
            cbn in Heqs.
            cbn.
            repeat break_match_hyp_inv.
            -- destruct (uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ H Heqs0).
               exists x0. rewrite H0. reflexivity.
            -- break_match_goal; [eexists; eauto|].
               destruct (IHHeqo s eq_refl) as [s' EQ].
               exists s'. rewrite EQ. reflexivity.
          }
          destruct H as [s' EQ].
          rewrite EQ.
          cbn.
          apply orutt_raise; [intros; intro C; inversion C | cbn; auto].
        * cbn.
          rewrite map_monad_err_Forall2 in Heqs.
          break_match_goal; cbn.
          -- assert False.
             { revert s l0 Heqs Heqs0.
               induction Heqo; intros; [inversion Heqs0|].
               cbn in Heqs0.
               inversion Heqs; subst.
               repeat break_match_hyp_inv.
               ++ destruct (uvalue_to_dvalue_dvalue_refine_strict _ _ _ H H2) as [v [C _]].
                  rewrite Heqs1 in C.
                  inversion C.
               ++ eapply IHHeqo; eauto.
             }
             inversion H.
          -- apply orutt_Ret.
             unfold dvalue_refine_strict.
             cbn.
             erewrite map_dvalue_convert_strict_succeeds; eauto.
      + break_match_goal.
        * assert False by (eapply is_concrete_l_false; eauto).
          inversion H.
        * apply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
          { (* Pick uvalue *)
            apply orutt_trigger; cbn.
            -- unfold uvalue_refine_strict; cbn.
               break_match_goal.
               ++ rewrite map_monad_oom_Forall2 in Heqo0.
                  clear Heqb Heqb0.
                  assert (l0 = l).
                  { revert l0 Heqo0.
                    induction Heqo; intros; inversion Heqo0; subst; auto.
                    specialize (uvalue_refine_strict_R2_injective _ _ _ _ H H2) as [EQ _].
                    rewrite (EQ eq_refl) in *; clear EQ.
                    erewrite (IHHeqo l'0); eauto.
                  }
                  rewrite H; auto.
               ++  apply map_monad_OOM_fail in Heqo0.
                   destruct Heqo0 as [dv [HI HS]].
                   destruct (Forall2_In _ _ _ _ HI Heqo) as [dv' [_ C]].
                   rewrite HS in C. inversion C.
            -- intros [t1] [t2] [REF1 REF2].
               cbn; auto.
            --  intros o.
                intro C.
                inv C.
          }

          intros [r1] [r2] H0.
          cbn in *.
          apply orutt_Ret; auto.

    - (* Packed Structs *)
      break_match_hyp; inv HRS; cbn.
      rewrite map_monad_oom_Forall2 in Heqo.
      unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick.
      cbn.
      break_match_goal.
      + specialize (is_concrete_l fields l Heqo Heqb) as HL.
        rewrite HL.
        clear Heqb HL.
        break_match_goal.
        * assert (exists v, map_monad uvalue_to_dvalue l = inl v).
          { revert s Heqs.
            induction Heqo; intros; [inversion Heqs|].
            cbn in Heqs.
            cbn.
            repeat break_match_hyp_inv.
            -- destruct (uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ H Heqs0).
               exists x0. rewrite H0. reflexivity.
            -- break_match_goal; [eexists; eauto|].
               destruct (IHHeqo s eq_refl) as [s' EQ].
               exists s'. rewrite EQ. reflexivity.
          }
          destruct H as [s' EQ].
          rewrite EQ.
          cbn.
          apply orutt_raise; [intros; intro C; inversion C | cbn; auto].
        * cbn.
          rewrite map_monad_err_Forall2 in Heqs.
          break_match_goal; cbn.
          -- assert False.
             { revert s l0 Heqs Heqs0.
               induction Heqo; intros; [inversion Heqs0|].
               cbn in Heqs0.
               inversion Heqs; subst.
               repeat break_match_hyp_inv.
               ++ destruct (uvalue_to_dvalue_dvalue_refine_strict _ _ _ H H2) as [v [C _]].
                  rewrite Heqs1 in C.
                  inversion C.
               ++ eapply IHHeqo; eauto.
             }
             inversion H.
          -- apply orutt_Ret.
             unfold dvalue_refine_strict.
             cbn.
             erewrite map_dvalue_convert_strict_succeeds; eauto.
      + break_match_goal.
        * assert False by (eapply is_concrete_l_false; eauto).
          inversion H.
        * apply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
          { (* Pick uvalue *)
            apply orutt_trigger; cbn.
            -- unfold uvalue_refine_strict. cbn.

               break_match_goal.
               ++ rewrite map_monad_oom_Forall2 in Heqo0.
                  clear Heqb Heqb0.
                  assert (l0 = l).
                  { revert l0 Heqo0.
                    induction Heqo; intros; inversion Heqo0; subst; auto.
                    specialize (uvalue_refine_strict_R2_injective _ _ _ _ H H2) as [EQ _].
                    rewrite (EQ eq_refl) in *; clear EQ.
                    erewrite (IHHeqo l'0); eauto.
                  }
                  rewrite H; auto.
               ++  apply map_monad_OOM_fail in Heqo0.
                   destruct Heqo0 as [dv [HI HS]].
                   destruct (Forall2_In _ _ _ _ HI Heqo) as [dv' [_ C]].
                   rewrite HS in C. inversion C.
            -- intros [t1] [t2] [REF1 REF2].
               cbn; auto.
            --  intros o.
                intro C.
                inv C.
          }

          intros [r1] [r2] H0.
          cbn in *.
          apply orutt_Ret; auto.

    - (* Arrays *)
      break_match_hyp; inv HRS; cbn.
      rewrite map_monad_oom_Forall2 in Heqo.
      unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick.
      cbn.
      break_match_goal.
      + specialize (is_concrete_l elts l Heqo Heqb) as HL.
        rewrite HL.
        clear Heqb HL.
        break_match_goal.
        * assert (exists v, map_monad uvalue_to_dvalue l = inl v).
          { revert s Heqs.
            induction Heqo; intros; [inversion Heqs|].
            cbn in Heqs.
            cbn.
            repeat break_match_hyp_inv.
            -- destruct (uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ H Heqs0).
               exists x0. rewrite H0. reflexivity.
            -- break_match_goal; [eexists; eauto|].
               destruct (IHHeqo s eq_refl) as [s' EQ].
               exists s'. rewrite EQ. reflexivity.
          }
          destruct H as [s' EQ].
          rewrite EQ.
          cbn.
          apply orutt_raise; [intros; intro C; inversion C | cbn; auto].
        * cbn.
          rewrite map_monad_err_Forall2 in Heqs.
          break_match_goal; cbn.
          -- assert False.
             { revert s l0 Heqs Heqs0.
               induction Heqo; intros; [inversion Heqs0|].
               cbn in Heqs0.
               inversion Heqs; subst.
               repeat break_match_hyp_inv.
               ++ destruct (uvalue_to_dvalue_dvalue_refine_strict _ _ _ H H2) as [v [C _]].
                  rewrite Heqs1 in C.
                  inversion C.
               ++ eapply IHHeqo; eauto.
             }
             inversion H.
          -- apply orutt_Ret.
             unfold dvalue_refine_strict.
             cbn.
             erewrite map_dvalue_convert_strict_succeeds; eauto.
      + break_match_goal.
        * assert False by (eapply is_concrete_l_false; eauto).
          inversion H.
        * apply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
          { (* Pick uvalue *)
            apply orutt_trigger; cbn.
            -- unfold uvalue_refine_strict. cbn.

               break_match_goal.
               ++ rewrite map_monad_oom_Forall2 in Heqo0.
                  clear Heqb Heqb0.
                  assert (l0 = l).
                  { revert l0 Heqo0.
                    induction Heqo; intros; inversion Heqo0; subst; auto.
                    specialize (uvalue_refine_strict_R2_injective _ _ _ _ H H2) as [EQ _].
                    rewrite (EQ eq_refl) in *; clear EQ.
                    erewrite (IHHeqo l'0); eauto.
                  }
                  rewrite H; auto.
               ++  apply map_monad_OOM_fail in Heqo0.
                   destruct Heqo0 as [dv [HI HS]].
                   destruct (Forall2_In _ _ _ _ HI Heqo) as [dv' [_ C]].
                   rewrite HS in C. inversion C.
            -- intros [t1] [t2] [REF1 REF2].
               cbn; auto.
            --  intros o.
                intro C.
                inv C.
          }

          intros [r1] [r2] H0.
          cbn in *.
          apply orutt_Ret; auto.

    - (* Arrays *)
      break_match_hyp; inv HRS; cbn.
      rewrite map_monad_oom_Forall2 in Heqo.
      unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick.
      cbn.
      break_match_goal.
      + specialize (is_concrete_l elts l Heqo Heqb) as HL.
        rewrite HL.
        clear Heqb HL.
        break_match_goal.
        * assert (exists v, map_monad uvalue_to_dvalue l = inl v).
          { revert s Heqs.
            induction Heqo; intros; [inversion Heqs|].
            cbn in Heqs.
            cbn.
            repeat break_match_hyp_inv.
            -- destruct (uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ H Heqs0).
               exists x0. rewrite H0. reflexivity.
            -- break_match_goal; [eexists; eauto|].
               destruct (IHHeqo s eq_refl) as [s' EQ].
               exists s'. rewrite EQ. reflexivity.
          }
          destruct H as [s' EQ].
          rewrite EQ.
          cbn.
          apply orutt_raise; [intros; intro C; inversion C | cbn; auto].
        * cbn.
          rewrite map_monad_err_Forall2 in Heqs.
          break_match_goal; cbn.
          -- assert False.
             { revert s l0 Heqs Heqs0.
               induction Heqo; intros; [inversion Heqs0|].
               cbn in Heqs0.
               inversion Heqs; subst.
               repeat break_match_hyp_inv.
               ++ destruct (uvalue_to_dvalue_dvalue_refine_strict _ _ _ H H2) as [v [C _]].
                  rewrite Heqs1 in C.
                  inversion C.
               ++ eapply IHHeqo; eauto.
             }
             inversion H.
          -- apply orutt_Ret.
             unfold dvalue_refine_strict.
             cbn.
             erewrite map_dvalue_convert_strict_succeeds; eauto.
      + break_match_goal.
        * assert False by (eapply is_concrete_l_false; eauto).
          inversion H.
        * apply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
          { (* Pick uvalue *)
            apply orutt_trigger; cbn.
            -- unfold uvalue_refine_strict. cbn.

               break_match_goal.
               ++ rewrite map_monad_oom_Forall2 in Heqo0.
                  clear Heqb Heqb0.
                  assert (l0 = l).
                  { revert l0 Heqo0.
                    induction Heqo; intros; inversion Heqo0; subst; auto.
                    specialize (uvalue_refine_strict_R2_injective _ _ _ _ H H2) as [EQ _].
                    rewrite (EQ eq_refl) in *; clear EQ.
                    erewrite (IHHeqo l'0); eauto.
                  }
                  rewrite H; auto.
               ++  apply map_monad_OOM_fail in Heqo0.
                   destruct Heqo0 as [dv [HI HS]].
                   destruct (Forall2_In _ _ _ _ HI Heqo) as [dv' [_ C]].
                   rewrite HS in C. inversion C.
            -- intros [t1] [t2] [REF1 REF2].
               cbn; auto.
            --  intros o.
                intro C.
                inv C.
          }

          intros [r1] [r2] H0.
          cbn in *.
          apply orutt_Ret; auto.

    - (* GEP *)
      repeat break_match_hyp_inv.
      unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick in *;
      cbn;
      eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
      {
        apply orutt_trigger; cbn;
          [ first [ tauto
            | idtac
            ]
          | intros [t1] [t2] [REF1 REF2];
            cbn; auto
          | intros o CONTRA;
            inv CONTRA
          ].
        unfold uvalue_refine_strict.
        cbn.  rewrite Heqo.
        rewrite Heqo0.
        reflexivity.
      }

      intros [?r1] [?r2] H0;
        cbn in *;
        apply orutt_Ret; auto.

    - (* InsertElement *)
      repeat break_match_hyp_inv;
      unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick in *;
      cbn.

      eapply orutt_bind with (RR:=fun dv1 dv2 => dvalue_refine_strict (proj1_sig dv1) (proj1_sig dv2)).
      { (* Pick uvalue *)
        apply orutt_trigger; cbn.
        { unfold uvalue_refine_strict. cbn.
          rewrite Heqo.
          reflexivity.
        }
        intros [t1] [t2] [REF1 REF2].
        cbn; auto.
        intros o CONTRA.
        inv CONTRA.
      }

      intros [r1] [r2] H0.
      cbn in *.
      apply orutt_Ret; auto.

  Qed.


  Ltac simplify_expr odt :=
    destruct odt as [dt | ];
    cbn;
    try solve [
        solve_orutt_raise
      ];
    try (destruct dt; cbn;
         try solve [
             solve_orutt_raise
      ]).

  Lemma contains_undef_or_poison_E1_E2 :
    forall u2 u1,
      uvalue_refine_strict u1 u2 ->
      IS1.LP.Events.DV.contains_undef_or_poison u1 = contains_undef_or_poison u2.
  Proof.
    intros u2.
    induction u2; intros u1 REF;
      DVC.uvalue_refine_strict_inv REF;
      cbn; auto;
      try solve
        [ apply map_monad_oom_Forall2 in H1;
          induction H1; cbn; auto;
          setoid_rewrite H; cbn; auto;
          break_match; auto;
          eapply IHForall2;
          intros u H2 u1 H3;
          apply H;
          [right; auto| auto]
        | rewrite IHu2_1; eauto;
          rewrite IHu2_2; eauto
        | rewrite IHu2_1; eauto;
          rewrite IHu2_2; eauto;
          rewrite IHu2_3; eauto
        ].

    - rewrite IHu2; eauto.
      destruct (contains_undef_or_poison u2); cbn; auto.
      apply map_monad_oom_Forall2 in H2;
        induction H2; auto.
      cbn.
      erewrite H; cbn; auto.
      break_match; cbn; auto.
      apply IHForall2.
      intros idx H3 u1 H4.
      apply H; cbn; auto.
  Qed.

  Lemma dvalue_convert_strict_fin_inf_succeeds :
    forall dv_fin,
    {dv_inf & DVCrev.dvalue_convert_strict dv_fin = NoOom dv_inf}.
  Proof.
    intros dv_fin.
    induction dv_fin;
      try solve
        [eexists;
         cbn; eauto
        ].
    - pose proof (ACS.addr_convert_succeeds a) as (a_inf & CONV).
      exists (DVCrev.DV2.DVALUE_Addr a_inf).
      cbn.
      rewrite CONV; cbn; eauto.
    - pose proof (IPS.intptr_convert_succeeds x) as (x_inf & CONV).
      eexists.
      cbn.
      rewrite CONV; cbn; eauto.
    - induction fields.
      + exists (DVCrev.DV2.DVALUE_Struct []).
        cbn.
        reflexivity.
      + forward IHfields.
        { intros u X0.
          eapply X.
          right; auto.
        }

        destruct IHfields.
        cbn in e.
        break_match_hyp_inv.

        pose proof (X a).
        forward X0; cbn; auto.
        destruct X0 as (a'&A).
        exists (DVCrev.DV2.DVALUE_Struct (a' :: l)).

        cbn.
        rewrite A.
        rewrite Heqo.
        reflexivity.
    - induction fields.
      + exists (DVCrev.DV2.DVALUE_Packed_struct []).
        cbn.
        reflexivity.
      + forward IHfields.
        { intros u X0.
          eapply X.
          right; auto.
        }

        destruct IHfields.
        cbn in e.
        break_match_hyp_inv.

        pose proof (X a).
        forward X0; cbn; auto.
        destruct X0 as (a'&A).
        exists (DVCrev.DV2.DVALUE_Packed_struct (a' :: l)).

        cbn.
        rewrite A.
        rewrite Heqo.
        reflexivity.
    - induction elts.
      + exists (DVCrev.DV2.DVALUE_Array t []).
        cbn.
        reflexivity.
      + forward IHelts.
        { intros u X0.
          eapply X.
          right; auto.
        }

        destruct IHelts.
        cbn in e.
        break_match_hyp_inv.

        pose proof (X a).
        forward X0; cbn; auto.
        destruct X0 as (a'&A).
        exists (DVCrev.DV2.DVALUE_Array t (a' :: l)).

        cbn.
        rewrite A.
        rewrite Heqo.
        reflexivity.
    - induction elts.
      + exists (DVCrev.DV2.DVALUE_Vector t []).
        cbn.
        reflexivity.
      + forward IHelts.
        { intros u X0.
          eapply X.
          right; auto.
        }

        destruct IHelts.
        cbn in e.
        break_match_hyp_inv.

        pose proof (X a).
        forward X0; cbn; auto.
        destruct X0 as (a'&A).
        exists (DVCrev.DV2.DVALUE_Vector t (a' :: l)).

        cbn.
        rewrite A.
        rewrite Heqo.
        reflexivity.
  Qed.

  (* TODO: Should we move this? *)
  Definition fin_to_inf_dvalue (dv_fin : DVCrev.DV1.dvalue) : DVCrev.DV2.dvalue.
    pose proof dvalue_convert_strict_safe dv_fin as [dvi [CONV RCONV]].
    apply dvi.
  Defined.

  Lemma fin_to_inf_dvalue_ix :
    forall sz x,
      fin_to_inf_dvalue (@DVALUE_I sz x) =
        @DVCrev.DV2.DVALUE_I sz x.
  Proof.
    intros sz x.
    unfold fin_to_inf_dvalue.
    break_match_goal; clear Heqs; destruct p; clear e0;
      cbn in e; subst; inv e.
    auto.
  Qed.

  Definition intptr_fin_inf (x : IP.intptr) : IS1.LP.IP.intptr.
    pose proof intptr_convert_succeeds x.
    destruct H.
    apply x0.
  Defined.

  Lemma fin_to_inf_dvalue_iptr :
    forall x,
      fin_to_inf_dvalue (DVALUE_IPTR x) =
        DVCrev.DV2.DVALUE_IPTR (intptr_fin_inf x).
  Proof.
    intros x.
    unfold fin_to_inf_dvalue.
    break_match_goal; clear Heqs; destruct p; clear e0;
      cbn in e; subst; inv e.

    pose proof intptr_convert_succeeds x.
    destruct H.
    rewrite e in H0.
    inv H0.

    unfold intptr_fin_inf.
    break_match_goal.
    clear Heqs.
    congruence.
  Qed.

  (* TODO: Should we move this? *)
  Definition addr_refine addr_inf (addr_fin : addr) := AC1.addr_convert addr_inf = NoOom addr_fin.

  (* TODO: Should we move this? *)
  Definition fin_to_inf_addr (a : addr) : IS1.LP.ADDR.addr.
    unfold FinAddr.addr in a.
    unfold FiniteAddresses.Iptr in a.
    pose proof ACS.addr_convert_succeeds a as [a' _].
    exact a'.
  Defined.

  (* TODO: Move this *)
  Lemma addr_refine_fin_to_inf_addr :
    forall addr_fin,
      addr_refine (fin_to_inf_addr addr_fin) addr_fin.
  Proof.
    intros addr_fin.
    red. unfold fin_to_inf_addr.
    break_match_goal.
    clear Heqs.
    apply ACS.addr_convert_safe in e.
    auto.
  Qed.

  Lemma addr_convert_fin_to_inf_addr :
    forall addr_fin,
      AC1.addr_convert (fin_to_inf_addr addr_fin) = NoOom addr_fin.
  Proof.
    intros addr_fin.
    unfold fin_to_inf_addr in *.
    destruct (ACS.addr_convert_succeeds addr_fin).
    apply ACS.addr_convert_safe in e.
    auto.
  Qed.

  Lemma fin_to_inf_dvalue_addr :
    forall a,
      fin_to_inf_dvalue (DVALUE_Addr a) =
        DVCrev.DV2.DVALUE_Addr (fin_to_inf_addr a).
  Proof.
    intros a.
    unfold fin_to_inf_dvalue.
    break_match_goal; clear Heqs; destruct p; clear e0.
    cbn in e.
    break_match_hyp_inv.
    unfold fin_to_inf_addr.
    break_match_goal.
    clear Heqs.
    rewrite Heqo in e.
    inv e.
    auto.
  Qed.

  Lemma fin_to_inf_dvalue_float :
    forall f,
      fin_to_inf_dvalue (DVALUE_Float f) =
        DVCrev.DV2.DVALUE_Float f.
  Proof.
    intros a.
    unfold fin_to_inf_dvalue.
    break_match_goal; clear Heqs; destruct p; clear e0.
    cbn in e. inv e.
    reflexivity.
  Qed.

  Lemma fin_to_inf_dvalue_double :
    forall f,
      fin_to_inf_dvalue (DVALUE_Double f) =
        DVCrev.DV2.DVALUE_Double f.
  Proof.
    intros a.
    unfold fin_to_inf_dvalue.
    break_match_goal; clear Heqs; destruct p; clear e0.
    cbn in e. inv e.
    reflexivity.
  Qed.

  Lemma fin_to_inf_dvalue_poison :
    forall t,
      fin_to_inf_dvalue (DVALUE_Poison t) =
        DVCrev.DV2.DVALUE_Poison t.
  Proof.
    intros x.
    unfold fin_to_inf_dvalue.
    break_match_goal; clear Heqs; destruct p; clear e0;
      cbn in e; subst; inv e.
    auto.
  Qed.

  Lemma fin_to_inf_dvalue_oom :
    forall t,
      fin_to_inf_dvalue (DVALUE_Oom t) =
        DVCrev.DV2.DVALUE_Oom t.
  Proof.
    intros x.
    unfold fin_to_inf_dvalue.
    break_match_goal; clear Heqs; destruct p; clear e0;
      cbn in e; subst; inv e.
    auto.
  Qed.

  Lemma fin_to_inf_dvalue_none :
      fin_to_inf_dvalue DVALUE_None =
        DVCrev.DV2.DVALUE_None.
  Proof.
    unfold fin_to_inf_dvalue.
    break_match_goal; clear Heqs; destruct p; clear e0;
      cbn in e; subst; inv e.
    auto.
  Qed.

  Lemma fin_to_inf_dvalue_struct :
    forall elts,
      fin_to_inf_dvalue (DVALUE_Struct elts) =
        DVCrev.DV2.DVALUE_Struct (map fin_to_inf_dvalue elts).
  Proof.
    induction elts.
    - cbn.
      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs; destruct p; clear e0;
        cbn in e; subst; inv e.
      auto.
    - unfold fin_to_inf_dvalue in *.
      break_match_goal; clear Heqs; destruct p; clear e0;
        cbn in e; subst; inv e.
      break_match_hyp_inv.
      break_match_hyp_inv.
      break_match_hyp_inv.

      break_match_hyp_inv; clear Heqs; destruct p; clear e0.
      cbn in e; subst; inv e.

      break_match_hyp_inv.
      rewrite map_cons.
      inv Heqo.

      break_match_goal; clear Heqs; destruct p; clear e0.
      rewrite Heqo0 in e.
      inv e.
      auto.
  Qed.

  Lemma fin_to_inf_dvalue_packed_struct :
    forall elts,
      fin_to_inf_dvalue (DVALUE_Packed_struct elts) =
        DVCrev.DV2.DVALUE_Packed_struct (map fin_to_inf_dvalue elts).
  Proof.
    induction elts.
    - cbn.
      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs; destruct p; clear e0;
        cbn in e; subst; inv e.
      auto.
    - unfold fin_to_inf_dvalue in *.
      break_match_goal; clear Heqs; destruct p; clear e0;
        cbn in e; subst; inv e.
      break_match_hyp_inv.
      break_match_hyp_inv.
      break_match_hyp_inv.

      break_match_hyp_inv; clear Heqs; destruct p; clear e0.
      cbn in e; subst; inv e.

      break_match_hyp_inv.
      rewrite map_cons.
      inv Heqo.

      break_match_goal; clear Heqs; destruct p; clear e0.
      rewrite Heqo0 in e.
      inv e.
      auto.
  Qed.

  Lemma fin_to_inf_dvalue_array :
    forall elts t,
      fin_to_inf_dvalue (DVALUE_Array t elts) =
        DVCrev.DV2.DVALUE_Array t (map fin_to_inf_dvalue elts).
  Proof.
    induction elts; intros t.
    - cbn.
      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs; destruct p; clear e0;
        cbn in e; subst; inv e.
      auto.
    - unfold fin_to_inf_dvalue in *.
      break_match_goal; clear Heqs; destruct p; clear e0;
        cbn in e; subst; inv e.
      break_match_hyp_inv.
      break_match_hyp_inv.
      break_match_hyp_inv.
      rewrite map_cons.

      specialize (IHelts t).

      break_match_hyp_inv; clear Heqs; destruct p; clear e0.
      cbn in e; subst; inv e.

      break_match_hyp_inv.
      inv Heqo.

      break_match_goal; clear Heqs; destruct p; clear e0.
      rewrite Heqo0 in e.
      inv e.
      auto.
  Qed.

  Lemma fin_to_inf_dvalue_vector :
    forall elts t,
      fin_to_inf_dvalue (DVALUE_Vector t elts) =
        DVCrev.DV2.DVALUE_Vector t (map fin_to_inf_dvalue elts).
  Proof.
    induction elts; intros t.
    - cbn.
      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs; destruct p; clear e0;
        cbn in e; subst; inv e.
      auto.
    - unfold fin_to_inf_dvalue in *.
      break_match_goal; clear Heqs; destruct p; clear e0;
        cbn in e; subst; inv e.
      break_match_hyp_inv.
      break_match_hyp_inv.
      break_match_hyp_inv.
      rewrite map_cons.

      specialize (IHelts t).

      break_match_hyp_inv; clear Heqs; destruct p; clear e0.
      cbn in e; subst; inv e.

      break_match_hyp_inv.

      break_match_goal; clear Heqs; destruct p; clear e0.
      rewrite Heqo0 in e.
      inv e.

      inv Heqo.
      auto.
  Qed.

  Ltac rewrite_fin_to_inf_dvalue :=
    repeat
      first
      [ rewrite fin_to_inf_dvalue_ix
      | rewrite fin_to_inf_dvalue_iptr
      | rewrite fin_to_inf_dvalue_addr
      | rewrite fin_to_inf_dvalue_float
      | rewrite fin_to_inf_dvalue_double
      | rewrite fin_to_inf_dvalue_poison
      | rewrite fin_to_inf_dvalue_oom
      | rewrite fin_to_inf_dvalue_none
      | rewrite fin_to_inf_dvalue_array
      | rewrite fin_to_inf_dvalue_vector
      | rewrite fin_to_inf_dvalue_struct
      | rewrite fin_to_inf_dvalue_packed_struct
      ].

  Lemma dvalue_has_dtyp_fin_to_inf_dvalue :
    forall dv_fin t,
      dvalue_has_dtyp dv_fin t ->
      IS1.LP.Events.DV.dvalue_has_dtyp (fin_to_inf_dvalue dv_fin) t.
  Proof.
    intros dv_fin t TYP.
    induction TYP;
      rewrite_fin_to_inf_dvalue;
      try solve [ constructor; eauto ].
    - (* Structs *)
      induction H; cbn.
      + constructor; constructor.
      + constructor.
        constructor; eauto.
        inv IHForall2.
        auto.
    - (* Packed Structs *)
      induction H; cbn.
      + constructor; constructor.
      + constructor.
        constructor; eauto.
        inv IHForall2.
        auto.
    - (* Arrays *)
      constructor; eauto.
      { apply Forall_forall; eauto.
        intros x H2.
        apply in_map_iff in H2.
        destruct H2 as (?&?&?); subst.
        eauto.
      }

      rewrite length_map.
      auto.
    - (* Vectors *)
      constructor; eauto.
      { apply Forall_forall; eauto.
        intros x H3.
        apply in_map_iff in H3.
        destruct H3 as (?&?&?); subst.
        eauto.
      }

      rewrite length_map.
      auto.
  Qed.

  (* TODO: Should we move this? *)
  Definition fin_to_inf_uvalue (uv_fin : DVCrev.DV1.uvalue) : DVCrev.DV2.uvalue.
    pose proof uvalue_convert_strict_safe uv_fin as [uvi [CONV RCONV]].
    apply uvi.
  Defined.

  Lemma convert_fin_to_inf_uvalue_succeeds :
    forall {uv_fin},
      DVC.uvalue_convert_strict (fin_to_inf_uvalue uv_fin) = NoOom uv_fin.
  Proof.
    intros.
    unfold fin_to_inf_uvalue.
    destruct (uvalue_convert_strict_safe uv_fin).
    destruct p.
    rewrite e0.
    reflexivity.
  Qed.

  Lemma fin_to_inf_uvalue_refine_strict' :
    forall d_inf d_fin,
      DVC.uvalue_refine_strict d_inf d_fin ->
      d_inf = fin_to_inf_uvalue d_fin.
  Proof.
    intros d_inf d_fin H.
    rewrite DVC.uvalue_refine_strict_equation in H.
    unfold fin_to_inf_uvalue.
    break_match; cbn in *.
    destruct p.
    clear Heqs.

    revert d_fin H x e e0.
    induction d_inf; intros d_fin H' x' e e0; try rename H into H''; rename H' into H;
      try solve
        [ cbn in *; inv H;
          cbn in *; inv e;
          auto
        ].
    - cbn in *.
      break_match_hyp; inv H.
      cbn in *.
      break_match_hyp; inv e.
      cbn in *.
      break_match_hyp; inv e0.

      pose proof AC1.addr_convert_injective a a1 a0 Heqo Heqo1.
      subst.
      auto.
    - cbn in *; break_match_hyp; inv H.
      cbn in *; inv e.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; inv e0.
      cbn in *; break_match_hyp; inv H0.

      pose proof (IP.from_Z_injective _ _ _ Heqo Heqo1).
      apply IS1.LP.IP.to_Z_inj in H.
      subst.
      reflexivity.
    - cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv e0.

      revert l Heqo l0 Heqo1 H'' Heqo0.
      induction fields; intros l Heqo l0 Heqo1 H'' Heqo0.
      + cbn in *. inv Heqo.
        cbn in *. inv Heqo0.
        reflexivity.
      + rewrite map_monad_unfold in Heqo.
        cbn in *.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo0.
        cbn in *.
        break_match_hyp; inv Heqo0.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo1.
        cbn in *.
        break_match_hyp; inv Heqo1.
        break_match_hyp; inv H0.

        (* Show that a = u0 *)
        pose proof (H'' a (or_introl eq_refl) _ Heqo2 _ Heqo3 Heqo4); subst.

        specialize (IHfields _ eq_refl l Heqo1).
        forward IHfields; eauto.
        forward IHfields; eauto.
        inv IHfields.
        reflexivity.
    - cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv e0.

      revert l Heqo l0 Heqo1 H'' Heqo0.
      induction fields; intros l Heqo l0 Heqo1 H'' Heqo0.
      + cbn in *. inv Heqo.
        cbn in *. inv Heqo0.
        reflexivity.
      + rewrite map_monad_unfold in Heqo.
        cbn in *.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo0.
        cbn in *.
        break_match_hyp; inv Heqo0.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo1.
        cbn in *.
        break_match_hyp; inv Heqo1.
        break_match_hyp; inv H0.

        (* Show that a = u0 *)
        pose proof (H'' a (or_introl eq_refl) _ Heqo2 _ Heqo3 Heqo4); subst.

        specialize (IHfields _ eq_refl l Heqo1).
        forward IHfields; eauto.
        forward IHfields; eauto.
        inv IHfields.
        reflexivity.
    - cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv e0.

      revert l Heqo l0 Heqo1 H'' Heqo0.
      induction elts; intros l Heqo l0 Heqo1 H'' Heqo0.
      + cbn in *. inv Heqo.
        cbn in *. inv Heqo0.
        reflexivity.
      + rewrite map_monad_unfold in Heqo.
        cbn in *.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo0.
        cbn in *.
        break_match_hyp; inv Heqo0.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo1.
        cbn in *.
        break_match_hyp; inv Heqo1.
        break_match_hyp; inv H0.

        (* Show that a = u0 *)
        pose proof (H'' a (or_introl eq_refl) _ Heqo2 _ Heqo3 Heqo4); subst.

        specialize (IHelts _ eq_refl l Heqo1).
        forward IHelts; eauto.
        forward IHelts; eauto.
        inv IHelts.
        reflexivity.
    - cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv e0.

      revert l Heqo l0 Heqo1 H'' Heqo0.
      induction elts; intros l Heqo l0 Heqo1 H'' Heqo0.
      + cbn in *. inv Heqo.
        cbn in *. inv Heqo0.
        reflexivity.
      + rewrite map_monad_unfold in Heqo.
        cbn in *.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo0.
        cbn in *.
        break_match_hyp; inv Heqo0.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo1.
        cbn in *.
        break_match_hyp; inv Heqo1.
        break_match_hyp; inv H0.

        (* Show that a = u0 *)
        pose proof (H'' a (or_introl eq_refl) _ Heqo2 _ Heqo3 Heqo4); subst.

        specialize (IHelts _ eq_refl l Heqo1).
        forward IHelts; eauto.
        forward IHelts; eauto.
        inv IHelts.
        reflexivity.
    - (* IBinop *)
      cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv H1.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv e0.
      cbn in *; break_match_hyp; inv H0.

      erewrite IHd_inf1; eauto.
      erewrite IHd_inf2; eauto.
    - (* ICmp *)
      cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv H1.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv e0.
      cbn in *; break_match_hyp; inv H0.

      erewrite IHd_inf1; eauto.
      erewrite IHd_inf2; eauto.
    - (* FBinop *)
      cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv H1.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv e0.
      cbn in *; break_match_hyp; inv H0.

      erewrite IHd_inf1; eauto.
      erewrite IHd_inf2; eauto.
    - (* FCmp *)
      cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv H1.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv e0.
      cbn in *; break_match_hyp; inv H0.

      erewrite IHd_inf1; eauto.
      erewrite IHd_inf2; eauto.
    - (* Conversion *)
      cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv e0.

      erewrite IHd_inf; eauto.
    - (* GEP *)
      cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv H1.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv e0.
      cbn in *; break_match_hyp; inv H0.

      revert l Heqo l0 u0 Heqo1 H'' Heqo0 Heqo2 Heqo4 Heqo3.
      induction idxs; intros l Heqo l0 u0 Heqo1 H'' Heqo0 Heqo2 Heqo4 Heqo3.
      + cbn in *. inv Heqo0.
        cbn in *. inv Heqo2.
        erewrite IHd_inf; eauto.
      + rewrite map_monad_unfold in Heqo0.
        cbn in *.
        break_match_hyp; inv Heqo0.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo2.
        cbn in *.
        break_match_hyp; inv Heqo2.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo4.
        cbn in *.
        break_match_hyp; inv Heqo4.
        break_match_hyp; inv H0.

        (* Show that a = u0 *)
        pose proof (H'' a (or_introl eq_refl)_ Heqo5 _ Heqo6 Heqo7); subst.

        specialize (IHidxs l1 Heqo l _ Heqo1).
        repeat (forward IHidxs; eauto).
        inv IHidxs.
        reflexivity.
    - (* ExtractElement *)
      cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv H1.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv e0.
      cbn in *; break_match_hyp; inv H0.

      erewrite IHd_inf1; eauto.
      erewrite IHd_inf2; eauto.
    - (* InsertElement *)
      cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv H1.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv H1.
      cbn in *; break_match_hyp; inv e0.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv H1.

      erewrite IHd_inf1; eauto.
      erewrite IHd_inf2; eauto.
      erewrite IHd_inf3; eauto.
    - (* ShuffleVector *)
      cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv H1.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv H1.
      cbn in *; break_match_hyp; inv e0.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv H1.

      erewrite IHd_inf1; eauto.
      erewrite IHd_inf2; eauto.
      erewrite IHd_inf3; eauto.
    - (* ExtractValue *)
      cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv e0.

      erewrite IHd_inf; eauto.
    - (* InsertValue *)
      cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv H1.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv e0.
      cbn in *; break_match_hyp; inv H0.

      erewrite IHd_inf1; eauto.
      erewrite IHd_inf2; eauto.
    - (* Select *)
      cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv H1.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv H1.
      cbn in *; break_match_hyp; inv e0.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv H1.

      erewrite IHd_inf1; eauto.
      erewrite IHd_inf2; eauto.
      erewrite IHd_inf3; eauto.
    - (* ExtractByte *)
      cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv e0.

      erewrite IHd_inf; eauto.
    - (* ConcatBytes *)
      cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv e0.

      revert l Heqo l0 Heqo1 H'' Heqo0 Heqo.
      induction uvs; intros l Heqo l0 Heqo1 H'' Heqo0 Heqo2.
      + cbn in *. inv Heqo2.
        cbn in *. inv Heqo0.
        reflexivity.
      + rewrite map_monad_unfold in Heqo2.
        cbn in *.
        break_match_hyp; inv Heqo2.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo0.
        cbn in *.
        break_match_hyp; inv Heqo0.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo1.
        cbn in *.
        break_match_hyp; inv Heqo1.
        break_match_hyp; inv H0.

        (* Show that a = u0 *)
        pose proof (H'' a (or_introl eq_refl) _ Heqo3 _ Heqo4 Heqo5); subst.

        specialize (IHuvs l1 eq_refl l Heqo1).
        repeat (forward IHuvs; eauto).
        inv IHuvs.
        reflexivity.
  Qed.

  (* TODO: Move these *)
  Lemma fin_to_inf_dvalue_refine_strict :
    forall d,
      dvalue_refine_strict (fin_to_inf_dvalue d) d.
  Proof.
    intros d.
    rewrite dvalue_refine_strict_equation.
    unfold fin_to_inf_dvalue.
    break_match; cbn in *.
    destruct p.
    auto.
  Qed.

  Lemma fin_to_inf_uvalue_refine_strict :
    forall u,
      uvalue_refine_strict (fin_to_inf_uvalue u) u.
  Proof.
    intros u.
    rewrite uvalue_refine_strict_equation.
    unfold fin_to_inf_uvalue.
    break_match; cbn in *.
    destruct p.
    auto.
  Qed.

  Lemma fin_to_inf_dvalue_refine_strict' :
    forall d_inf d_fin,
      DVC.dvalue_refine_strict d_inf d_fin ->
      d_inf = fin_to_inf_dvalue d_fin.
  Proof.
    intros d_inf d_fin H.
    rewrite DVC.dvalue_refine_strict_equation in H.
    unfold fin_to_inf_dvalue.
    break_match; cbn in *.
    destruct p.
    clear Heqs.

    revert d_fin H x e e0.
    induction d_inf; intros d_fin H' x' e e0; try rename H into H''; rename H' into H;
      try solve
        [ cbn in *; inv H;
          cbn in *; inv e;
          auto
        ].
    - cbn in *.
      break_match_hyp; inv H.
      cbn in *.
      break_match_hyp; inv e.
      cbn in *.
      break_match_hyp; inv e0.

      pose proof AC1.addr_convert_injective a a1 a0 Heqo Heqo1.
      subst.
      auto.
    - cbn in *; break_match_hyp; inv H.
      cbn in *; inv e.
      cbn in *; break_match_hyp; inv H0.
      cbn in *; break_match_hyp; inv e0.

      pose proof (IP.from_Z_injective _ _ _ Heqo Heqo1).
      apply IS1.LP.IP.to_Z_inj in H.
      subst.
      reflexivity.
    - cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv e0.

      revert l Heqo l0 Heqo1 H'' Heqo0.
      induction fields; intros l Heqo l0 Heqo1 H'' Heqo0.
      + cbn in *. inv Heqo.
        cbn in *. inv Heqo0.
        reflexivity.
      + rewrite map_monad_unfold in Heqo.
        cbn in *.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo0.
        cbn in *.
        break_match_hyp; inv Heqo0.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo1.
        cbn in *.
        break_match_hyp; inv Heqo1.
        break_match_hyp; inv H0.

        (* Show that a = u0 *)
        pose proof (H'' a (or_introl eq_refl) _ Heqo2 _ Heqo3 Heqo4); subst.

        specialize (IHfields _ eq_refl l Heqo1).
        forward IHfields; eauto.
        forward IHfields; eauto.
        inv IHfields.
        reflexivity.
    - cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv e0.

      revert l Heqo l0 Heqo1 H'' Heqo0.
      induction fields; intros l Heqo l0 Heqo1 H'' Heqo0.
      + cbn in *. inv Heqo.
        cbn in *. inv Heqo0.
        reflexivity.
      + rewrite map_monad_unfold in Heqo.
        cbn in *.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo0.
        cbn in *.
        break_match_hyp; inv Heqo0.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo1.
        cbn in *.
        break_match_hyp; inv Heqo1.
        break_match_hyp; inv H0.

        (* Show that a = u0 *)
        pose proof (H'' a (or_introl eq_refl) _ Heqo2 _ Heqo3 Heqo4); subst.

        specialize (IHfields _ eq_refl l Heqo1).
        forward IHfields; eauto.
        forward IHfields; eauto.
        inv IHfields.
        reflexivity.
    - cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv e0.

      revert l Heqo l0 Heqo1 H'' Heqo0.
      induction elts; intros l Heqo l0 Heqo1 H'' Heqo0.
      + cbn in *. inv Heqo.
        cbn in *. inv Heqo0.
        reflexivity.
      + rewrite map_monad_unfold in Heqo.
        cbn in *.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo0.
        cbn in *.
        break_match_hyp; inv Heqo0.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo1.
        cbn in *.
        break_match_hyp; inv Heqo1.
        break_match_hyp; inv H0.

        (* Show that a = u0 *)
        pose proof (H'' a (or_introl eq_refl) _ Heqo2 _ Heqo3 Heqo4); subst.

        specialize (IHelts _ eq_refl l Heqo1).
        forward IHelts; eauto.
        forward IHelts; eauto.
        inv IHelts.
        reflexivity.
    - cbn in *; break_match_hyp; inv H.
      cbn in *; break_match_hyp; inv e.
      cbn in *; break_match_hyp; inv e0.

      revert l Heqo l0 Heqo1 H'' Heqo0.
      induction elts; intros l Heqo l0 Heqo1 H'' Heqo0.
      + cbn in *. inv Heqo.
        cbn in *. inv Heqo0.
        reflexivity.
      + rewrite map_monad_unfold in Heqo.
        cbn in *.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo0.
        cbn in *.
        break_match_hyp; inv Heqo0.
        break_match_hyp; inv H0.

        rewrite map_monad_unfold in Heqo1.
        cbn in *.
        break_match_hyp; inv Heqo1.
        break_match_hyp; inv H0.

        (* Show that a = u0 *)
        pose proof (H'' a (or_introl eq_refl) _ Heqo2 _ Heqo3 Heqo4); subst.

        specialize (IHelts _ eq_refl l Heqo1).
        forward IHelts; eauto.
        forward IHelts; eauto.
        inv IHelts.
        reflexivity.
  Qed.

  Definition uvalue_concretize_u_fin_inf_inclusion uv_inf uv_fin :=
    forall res,
      IS2.MEM.CP.CONC.concretize_u uv_fin res ->
      IS1.MEM.CP.CONC.concretize_u uv_inf (fmap fin_to_inf_dvalue res).

  Definition uvalue_concretize_fin_inf_inclusion uv_inf uv_fin :=
    forall dv_fin,
      IS2.MEM.CP.CONC.concretize uv_fin dv_fin ->
      IS1.MEM.CP.CONC.concretize uv_inf (fin_to_inf_dvalue dv_fin).

  Definition uvalue_concretize_inf_fin_inclusion uv_inf uv_fin :=
    forall dv_inf,
      IS1.MEM.CP.CONC.concretize uv_inf dv_inf ->
      exists dv_fin,
        dvalue_refine_strict dv_inf dv_fin /\
          IS2.MEM.CP.CONC.concretize uv_fin dv_fin.

  (* TODO: Move this *)
  Lemma dvalue_convert_strict_fin_inf_succeeds_fin_to_inf_dvalue :
    forall x y,
      DVCrev.dvalue_convert_strict x = NoOom y ->
      fin_to_inf_dvalue x = y.
  Proof.
    intros x y CONV.
    unfold fin_to_inf_dvalue.
    break_match_goal.
    break_match_goal.
    clear Heqs.
    subst.
    rewrite CONV in e.
    inv e; auto.
  Qed.

  (* TODO: Move this *)
  Lemma dvalue_convert_strict_struct_map :
    forall fields_fin res,
      DVCrev.dvalue_convert_strict (DVALUE_Struct fields_fin) = NoOom res ->
      res = (IS1.LP.Events.DV.DVALUE_Struct (map fin_to_inf_dvalue fields_fin)).
  Proof.
    intros fields_fin res CONV.
    cbn in CONV.
    break_match_hyp_inv.
    apply map_monad_oom_Forall2 in Heqo.
    induction Heqo.
    - cbn. reflexivity.
    - rewrite map_cons.
      apply dvalue_convert_strict_fin_inf_succeeds_fin_to_inf_dvalue in H.
      rewrite H.
      inv IHHeqo.
      reflexivity.
  Qed.

  (* TODO: Move this *)
  Lemma dvalue_convert_strict_packed_struct_map :
    forall fields_fin res,
      DVCrev.dvalue_convert_strict (DVALUE_Packed_struct fields_fin) = NoOom res ->
      res = (IS1.LP.Events.DV.DVALUE_Packed_struct (map fin_to_inf_dvalue fields_fin)).
  Proof.
    intros fields_fin res CONV.
    cbn in CONV.
    break_match_hyp_inv.
    apply map_monad_oom_Forall2 in Heqo.
    induction Heqo.
    - cbn. reflexivity.
    - rewrite map_cons.
      apply dvalue_convert_strict_fin_inf_succeeds_fin_to_inf_dvalue in H.
      rewrite H.
      inv IHHeqo.
      reflexivity.
  Qed.

  (* TODO: Move this *)
  Lemma dvalue_convert_strict_array_map :
    forall fields_fin res t,
      DVCrev.dvalue_convert_strict (DVALUE_Array t fields_fin) = NoOom res ->
      res = (IS1.LP.Events.DV.DVALUE_Array t (map fin_to_inf_dvalue fields_fin)).
  Proof.
    intros fields_fin res t CONV.
    cbn in CONV.
    break_match_hyp_inv.
    apply map_monad_oom_Forall2 in Heqo.
    induction Heqo.
    - cbn. reflexivity.
    - rewrite map_cons.
      apply dvalue_convert_strict_fin_inf_succeeds_fin_to_inf_dvalue in H.
      rewrite H.
      inv IHHeqo.
      reflexivity.
  Qed.

  (* TODO: Move this *)
  Lemma dvalue_convert_strict_vector_map :
    forall fields_fin res t,
      DVCrev.dvalue_convert_strict (DVALUE_Vector t fields_fin) = NoOom res ->
      res = (IS1.LP.Events.DV.DVALUE_Vector t (map fin_to_inf_dvalue fields_fin)).
  Proof.
    intros fields_fin res t CONV.
    cbn in CONV.
    break_match_hyp_inv.
    apply map_monad_oom_Forall2 in Heqo.
    induction Heqo.
    - cbn. reflexivity.
    - rewrite map_cons.
      apply dvalue_convert_strict_fin_inf_succeeds_fin_to_inf_dvalue in H.
      rewrite H.
      inv IHHeqo.
      reflexivity.
  Qed.

  (* TODO: move / generalize these *)
  Lemma map_monad_ErrUbOomProp_forall2 :
    forall {A B} (f : A -> ErrUbOomProp B) l res,
      @map_monad ErrUbOomProp Monad_ErrUbOomProp _ _ f l (ret res) <->
        Forall2 (fun a b => f a (ret b)) l res.
  Proof.
    intros A B f.
    induction l; intros res.
    - split; intros MAP.
      + cbn in *.
        inv MAP.
        auto.
      + inv MAP.
        reflexivity.
    - split; intros MAP.
      + rewrite map_monad_unfold in MAP.
        cbn in MAP.
        repeat red in MAP.
        destruct MAP as (?&?&?&?&?).

        cbn in H0.
        destruct_err_ub_oom x; cbn in *; subst; inv H0.

        destruct H1 as [[] | H1].
        specialize (H1 x1 eq_refl).
        repeat red in H1.
        destruct H1 as (?&?&?&?&?).
        cbn in H1.

        destruct_err_ub_oom x; cbn in *; subst; inv H1;
          rewrite <- H5 in H3; inv H3.

        destruct H2 as [[] | H2].
        specialize (H2 x3 eq_refl).
        rewrite <- H2 in H5.
        cbn in H5.
        rewrite H2 in H5.
        rewrite <- H2 in H4.
        cbn in H4.
        inv H4.

        constructor.
        2: {
          apply IHl.
          apply H0.
        }

        auto.
      + inv MAP.
        rewrite map_monad_unfold.
        repeat red.
        exists (ret y).
        exists (fun x => ret (x :: l')).

        apply IHl in H3.
        split; eauto.
        split; eauto.

        right.
        intros a0 H.
        cbn in H; subst.
        repeat red.
        exists (ret l').
        exists (fun l => ret (a0 :: l)).
        split; eauto.
        split; cbn; eauto.
  Qed.

  (* TODO: Move this *)
  Lemma map_monad_ErrUbOomProp_length :
    forall {A B : Type} {xs : list A} {f : A -> ErrUbOomProp B} {res},
      @map_monad ErrUbOomProp Monad_ErrUbOomProp A B f xs (ret res) ->
      length xs = length res.
  Proof.
    intros A B xs f res MAP.
    generalize dependent res.
    induction xs; intros res MAP.
    - cbn in *; inv MAP; reflexivity.
    - rewrite map_monad_unfold in MAP.
      repeat red in MAP.
      destruct MAP as (?&?&?&?&?).
      destruct_err_ub_oom x; subst; cbn in H0; inv H0.
      destruct H1 as [[] | H1].
      specialize (H1 x1 eq_refl).
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; rewrite <- H1 in H3; inv H3.
      cbn in *.
      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).
      rewrite <- H2 in H1.
      cbn in H1.
      rewrite <- H2 in H5.
      cbn in H5.
      inv H5.
      cbn.
      apply IHxs in H0.
      lia.
  Qed.

  (* TODO: Move this *)
  Lemma map_monad_orutt :
    forall {V} (elts : list V) {OOM E1 E2} `{OOME : OOM -< E2} {R1 R2} (pre : prerel E1 E2) (post : postrel E1 E2) (RR: R1 -> R2 -> Prop) (denote1 : V -> itree E1 R1) (denote2 : V -> itree E2 R2),
      (forall e,
          orutt pre post RR (denote1 e) (denote2 e) (OOM:=OOM)) ->
      orutt pre post (Forall2 RR) (map_monad denote1 elts) (map_monad denote2 elts) (OOM:=OOM).
  Proof.
    intros V elts.
    induction elts; intros OOM E1 E2 OOME R1 R2 pre post RR denote1 denote2 H.
    - cbn.
      apply orutt_Ret.
      constructor.
    - cbn.
      eapply orutt_bind; eauto.
      intros r1 r2 H0.
      eapply orutt_bind; eauto.
      intros r0 r3 H1.
      eapply orutt_Ret.
      constructor; auto.
  Qed.

  (* TODO: move this *)
  Lemma map_monad_orutt2 :
    forall {V1 V2} (elts1 : list V1) (elts2 : list V2) {OOM E1 E2} `{OOME : OOM -< E2} {R1 R2} (pre : prerel E1 E2) (post : postrel E1 E2) (VV : V1 -> V2 -> Prop) (RR: R1 -> R2 -> Prop) (denote1 : V1 -> itree E1 R1) (denote2 : V2 -> itree E2 R2),
      (Forall2 VV elts1 elts2) ->
      (forall e1 e2,
          VV e1 e2 ->
          orutt pre post RR (denote1 e1) (denote2 e2) (OOM:=OOM)) ->
      orutt pre post (Forall2 RR) (map_monad denote1 elts1) (map_monad denote2 elts2) (OOM:=OOM).
  Proof.
    intros V1 V2 elts1 elts2 OOM E1 E2 OOME R1 R2 pre post VV RR denote1 denote2 VVS H.
    induction VVS.
    - cbn.
      apply orutt_Ret.
      constructor.
    - repeat rewrite map_monad_unfold.
      eapply orutt_bind; eauto.

      intros r1 r2 H1.
      eapply orutt_bind; eauto.

      intros r0 r3 H2.
      eapply orutt_Ret.
      constructor; auto.
  Qed.

  Lemma GlobalRead_exp_E_E1E2_rutt :
    forall g,
      rutt exp_E_refine_strict exp_E_res_refine_strict dvalue_refine_strict (trigger (GlobalRead g)) (trigger (GlobalRead g)).
  Proof.
    intros g.
    apply rutt_trigger.
    cbn. auto.

    intros t1 t2 H.
    cbn in H.
    tauto.
  Qed.

  Lemma GlobalRead_L0_E1E2_rutt :
    forall g,
      rutt event_refine_strict event_res_refine_strict dvalue_refine_strict (trigger (GlobalRead g)) (trigger (GlobalRead g)).
  Proof.
    intros g.
    apply rutt_trigger.
    cbn. auto.

    intros t1 t2 H.
    cbn in H.
    tauto.
  Qed.

  Lemma Store_E1E2_rutt :
    forall dt r1 r2 r3 r4,
      dvalue_refine_strict r1 r2 ->
      uvalue_refine_strict r3 r4 ->
      rutt exp_E_refine_strict exp_E_res_refine_strict eq
        (trigger (IS1.LP.Events.Store dt r1 r3))
        (trigger (IS2.LP.Events.Store dt r2 r4)).
  Proof.
    intros dt r1 r2 r3 r4 R1R2 R3R4.
    apply rutt_trigger.
    cbn. tauto.

    intros [] [] _.
    reflexivity.
  Qed.

  (* TODO: move this! Probably somewhere that I get a version for each language? *)
  Ltac solve_dec_oom :=
    let s := fresh "s" in
    first [intros ? s | intros s];
    repeat destruct s;
    try solve
      [
        left;
        intros o CONTRA;
        inv CONTRA
      ];
    right;
    eexists; reflexivity.

  Lemma exp_E_dec_oom :
    forall A (e : exp_E A), {forall o : OOME A, e <> subevent _ o} + {exists o : OOME A, e = subevent _ o}.
  Proof.
    solve_dec_oom.
  Qed.

  (* TODO: move this! *)
  Lemma L0'_dec_oom :
    forall A (e : L0' A), {forall o : OOME A, e <> subevent _ o} + {exists o : OOME A, e = subevent _ o}.
  Proof.
    solve_dec_oom.
  Qed.

  (* TODO: move this! *)
  Lemma L0_dec_oom :
    forall A (e : L0 A), {forall o : OOME A, e <> subevent _ o} + {exists o : OOME A, e = subevent _ o}.
  Proof.
    solve_dec_oom.
  Qed.

  Definition function_denotation_refine_strict : IS1.LLVM.D.function_denotation -> IS2.LLVM.D.function_denotation -> Prop.
  Proof.
    intros d1 d2.
    unfold function_denotation in *.
    unfold IS1.LLVM.D.function_denotation in *.

    refine (forall args1 args2,
               Forall2 uvalue_refine_strict args1 args2 ->
               orutt L0'_refine_strict L0'_res_refine_strict uvalue_refine_strict
                 (d1 args1)
                 (d2 args2)
                 (OOM:=OOME)
           ).
  Defined.

  (* TODO: Move this *)
  Lemma eval_int_op_ix_fin_inf :
    forall sz v1 v2 iop res_fin res_inf,
      @eval_int_op err_ub_oom (@Integers.int sz) (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@VIntVMemInt (@Integers.int sz) (@VInt_Bounded sz)) (@ToDvalue_Int sz)
        iop v1 v2 = success_unERR_UB_OOM res_fin ->
      DVCrev.dvalue_convert_strict res_fin = NoOom res_inf ->
      @IS1.LP.Events.DV.eval_int_op err_ub_oom (@Integers.int sz)
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@VIntVMemInt (@Integers.int sz) (@VInt_Bounded sz)) (@IS1.LP.Events.DV.ToDvalue_Int sz)
        iop v1 v2 = success_unERR_UB_OOM res_inf.
  Proof.
    intros sz v1 v2 iop res_fin res_inf EVAL CONV.
    destruct iop.
    1-3:
      try solve
        [ cbn in *;
          repeat break_match_hyp_inv; cbn in *;
          inv CONV;
          cbn in *; reflexivity
        ].

    { cbn in *.
      break_match_hyp_inv.
      cbn in CONV; inv CONV; cbn; auto.
      break_match_hyp_inv.
      cbn in CONV; inv CONV; cbn; auto.
      destruct nsw.
      2: {
        cbn in H1; inv H1; cbn.
        cbn in CONV;
          inv CONV; cbn; auto.
      }

      break_match_hyp;
        cbn in H1; inv H1; cbn;
        cbn in CONV;
        inv CONV; cbn; auto.
    }

    all: try solve
           [ cbn in *;
             repeat break_match_hyp_inv; cbn in *;
             cbn in CONV; inv CONV;
             cbn in *; reflexivity
           ].

    all: try solve
           [ cbn in *;
             repeat break_match_hyp_inv; cbn in *; inv EVAL;
             cbn in CONV; inv CONV;
             cbn in *; reflexivity
           ].
  Qed.

  (* TODO: Move this *)
  Lemma eval_int_op_iptr_fin_inf :
    forall v1_fin v2_fin v1_inf v2_inf iop res_fin res_inf,
      @eval_int_op err_ub_oom IP.intptr (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        VMemInt_intptr' ToDvalue_intptr
        iop v1_fin v2_fin = success_unERR_UB_OOM res_fin ->
      IS1.LP.IP.from_Z (IP.to_Z v1_fin) = NoOom v1_inf ->
      IS1.LP.IP.from_Z (IP.to_Z v2_fin) = NoOom v2_inf ->
      DVCrev.dvalue_convert_strict res_fin = NoOom res_inf ->
      @IS1.LP.Events.DV.eval_int_op err_ub_oom IS1.LP.IP.intptr
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        IS1.LP.Events.DV.VMemInt_intptr' IS1.LP.Events.DV.ToDvalue_intptr
        iop v1_inf v2_inf = success_unERR_UB_OOM res_inf.
  Proof.
    intros v1_fin v2_fin v1_inf v2_inf iop res_fin res_inf
      EVAL LIFT1 LIFT2 CONV.

    assert (IP.to_Z v1_fin = IS1.LP.IP.to_Z v1_inf) as V1.
    { erewrite IS1.LP.IP.from_Z_to_Z; eauto. }

    assert (IP.to_Z v2_fin = IS1.LP.IP.to_Z v2_inf) as V2.
    { erewrite IS1.LP.IP.from_Z_to_Z; eauto. }

    destruct iop.
    - (* Add *)
      cbn in *.
      repeat rewrite VMEM_IP_PROP1.madd_carry_zero, VMEM_IP_PROP1.madd_overflow_zero.
      repeat rewrite VMEM_IP_PROP2.madd_carry_zero, VMEM_IP_PROP2.madd_overflow_zero in EVAL.
      setoid_rewrite VMEM_IP_PROP1.mequ_zero_one_false.
      setoid_rewrite VMEM_IP_PROP2.mequ_zero_one_false in EVAL.
      repeat rewrite Bool.andb_false_r.
      repeat rewrite Bool.andb_false_r in EVAL.
      cbn in *.

      remember (lift_OOM (madd v1_fin v2_fin)) as add_result.
      destruct_err_ub_oom add_result; inv EVAL.
      symmetry in Heqadd_result.
      destruct (madd v1_fin v2_fin) eqn:HADD; inv Heqadd_result.

      cbn in CONV.
      break_match_hyp_inv.

      pose proof VMEM_REF.madd_refine _ _ _ v1_inf v2_inf V1 V2 HADD as (?&?&?).
      setoid_rewrite H. cbn.
      rewrite H0 in Heqo.
      rewrite IS1.LP.IP.to_Z_from_Z in Heqo.
      inv Heqo.
      reflexivity.
    - (* Sub *)
      cbn in *.
      repeat rewrite VMEM_IP_PROP1.msub_borrow_zero, VMEM_IP_PROP1.msub_overflow_zero.
      repeat rewrite VMEM_IP_PROP2.msub_borrow_zero, VMEM_IP_PROP2.msub_overflow_zero in EVAL.
      setoid_rewrite VMEM_IP_PROP1.mequ_zero_one_false.
      setoid_rewrite VMEM_IP_PROP2.mequ_zero_one_false in EVAL.
      repeat rewrite Bool.andb_false_r.
      repeat rewrite Bool.andb_false_r in EVAL.
      cbn in *.

      remember (lift_OOM (msub v1_fin v2_fin)) as sub_result.
      destruct_err_ub_oom sub_result; inv EVAL.
      symmetry in Heqsub_result.
      destruct (msub v1_fin v2_fin) eqn:HSUB; inv Heqsub_result.

      cbn in CONV.
      break_match_hyp_inv.

      epose proof VMEM_REF.msub_refine _ _ _ v1_inf v2_inf V1 V2 HSUB as (?&?&?).
      setoid_rewrite H. cbn.
      rewrite H0 in Heqo.
      rewrite IS1.LP.IP.to_Z_from_Z in Heqo.
      inv Heqo.
      reflexivity.
    - (* Mul *)
      cbn in *.
      destruct mbitwidth; cbn in EVAL.
      2: {
        remember (lift_OOM (mmul v1_fin v2_fin)) as mul_result.
        destruct_err_ub_oom mul_result; inv EVAL.
        symmetry in Heqmul_result.
        destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.

        cbn in H0.
        setoid_rewrite IP.VMemInt_intptr_dtyp in H0.
        setoid_rewrite dtyp_eqb_refl in H0.
        break_match_hyp_inv.

        cbn in CONV.
        move CONV after Heqb.
        break_match_hyp_inv.

        epose proof VMEM_REF.mmul_refine _ _ _ v1_inf v2_inf V1 V2 HMUL as (?&?&?&?).
        rewrite H0 in Heqo.
        rewrite IS1.LP.IP.to_Z_from_Z in Heqo.
        inv Heqo.
        repeat setoid_rewrite H. cbn.
        break_match_goal; try reflexivity.
        setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
        setoid_rewrite dtyp_eqb_refl.
        break_match_goal; try reflexivity.
        setoid_rewrite Heqb1 in H1.
        inv H1.
      }

      break_match_hyp_inv.

      { remember (lift_OOM (mmul v1_fin v2_fin)) as mul_result.
        destruct_err_ub_oom mul_result; inv H0.
        symmetry in Heqmul_result.
        destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.

        cbn in CONV.
        move CONV after Heqb.
        repeat break_match_hyp_inv.

        epose proof VMEM_REF.mmul_refine _ _ _ v1_inf v2_inf V1 V2 HMUL as (?&?&?&?).
        rewrite H0 in Heqo.
        rewrite IS1.LP.IP.to_Z_from_Z in Heqo.
        inv Heqo.
        repeat setoid_rewrite H. cbn.
        break_match_goal; try reflexivity.
        setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
        setoid_rewrite dtyp_eqb_refl.
        break_match_goal; try reflexivity.

        setoid_rewrite Heqb0 in H1.
        inv H1.
      }

      break_match_goal.
      {
        remember (lift_OOM (mmul v1_fin v2_fin)) as mul_result.
        destruct_err_ub_oom mul_result; inv H0.
        symmetry in Heqmul_result.
        destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.
        epose proof VMEM_REF.mmul_refine _ _ _ v1_inf v2_inf V1 V2 HMUL as (?&?&?&?).
        setoid_rewrite H.
        cbn.

        setoid_rewrite IP.VMemInt_intptr_dtyp in H1.
        rewrite dtyp_eqb_refl in H1.
        setoid_rewrite VMEM_REF.munsigned_refine in H1; eauto.
        rewrite H2 in H1.
        cbn in *.
        inv H1.

        cbn in CONV.
        break_match_hyp_inv.
        rewrite H0 in Heqo.
        rewrite IS1.LP.IP.to_Z_from_Z in Heqo.
        inv Heqo; auto.
      }

      remember (lift_OOM (mmul v1_fin v2_fin)) as mul_result.
      destruct_err_ub_oom mul_result; inv H0.
      symmetry in Heqmul_result.
      destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.
      epose proof VMEM_REF.mmul_refine _ _ _ v1_inf v2_inf V1 V2 HMUL as (?&?&?&?).
      setoid_rewrite H.
      cbn.
      setoid_rewrite H2.

      setoid_rewrite IP.VMemInt_intptr_dtyp in H1.
      setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
      rewrite dtyp_eqb_refl.
      rewrite dtyp_eqb_refl in H1.
      setoid_rewrite VMEM_REF.munsigned_refine in H1; eauto.
      rewrite H2 in H1.
      cbn in *.
      inv H1.

      cbn in CONV.
      break_match_hyp_inv.
      rewrite H0 in Heqo.
      rewrite IS1.LP.IP.to_Z_from_Z in Heqo.
      inv Heqo; auto.
    - (* Shl *)
      cbn in *.
      destruct (mshl v1_fin v2_fin) eqn:HSHL;
        cbn in *; inv EVAL.

      epose proof VMEM_REF.mshl_refine _ _ _ v1_inf v2_inf V1 V2 HSHL as (?&?&?).
      setoid_rewrite H; cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in H0.
      setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
      setoid_rewrite dtyp_eqb_refl.
      setoid_rewrite dtyp_eqb_refl in H0.
      setoid_rewrite VMEM_REF.munsigned_refine in H0; eauto.
      break_match_hyp_inv.
      setoid_rewrite Heqb.
      cbn.
      cbn in CONV.
      break_match_hyp_inv.
      rewrite H1 in Heqo.
      rewrite IS1.LP.IP.to_Z_from_Z in Heqo.
      inv Heqo; auto.
    - (* UDiv *)
      cbn.
      cbn in EVAL.
      setoid_rewrite VMEM_REF.munsigned_refine in EVAL; eauto.
      break_match_hyp_inv.
      setoid_rewrite Heqb.
      setoid_rewrite VMEM_REF.munsigned_refine in H0; eauto.
      break_match_hyp_inv;
        setoid_rewrite Heqb0;
        cbn in CONV; inv CONV.
      + setoid_rewrite IP.VMemInt_intptr_dtyp;
          setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
        reflexivity.
      + break_match_hyp_inv.
        remember (mdivu v1_fin v2_fin) as div_res.
        symmetry in Heqdiv_res.
        pose proof VMEM_REF.mdivu_refine _ _ _ _ _ V1 V2 Heqdiv_res
          as (?&?&?).
        setoid_rewrite H.
        rewrite H0 in Heqo.
        rewrite IS1.LP.IP.to_Z_from_Z in Heqo.
        inv Heqo.
        auto.
    - (* SDiv *)
      cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL.
      setoid_rewrite dtyp_eqb_refl in EVAL.
      inv EVAL.
    - (* LShr *)
      cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL.
      setoid_rewrite dtyp_eqb_refl in EVAL.
      setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
      setoid_rewrite dtyp_eqb_refl.
      cbn in *.
      rewrite Bool.andb_false_r in *.
      setoid_rewrite VMEM_REF.munsigned_refine in EVAL; eauto.
      break_match_hyp_inv; setoid_rewrite Heqb;
        cbn in CONV; inv CONV.
      + setoid_rewrite IP.VMemInt_intptr_dtyp;
          setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
        reflexivity.
      + break_match_hyp_inv.
        remember (mshru v1_fin v2_fin) as shru_res.
        symmetry in Heqshru_res.
        pose proof VMEM_REF.mshru_refine _ _ _ _ _ V1 V2 Heqshru_res
          as (?&?&?).
        setoid_rewrite H.
        rewrite H0 in Heqo.
        rewrite IS1.LP.IP.to_Z_from_Z in Heqo.
        inv Heqo.
        auto.
    - (* AShr *)
      cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL.
      setoid_rewrite dtyp_eqb_refl in EVAL.
      inv EVAL.
    - (* URem *)
      cbn in *.
      setoid_rewrite VMEM_REF.munsigned_refine in EVAL; eauto.
      break_match_hyp_inv.
      setoid_rewrite Heqb.
      cbn in CONV.
      break_match_hyp_inv.
      remember (mmodu v1_fin v2_fin) as res.
      symmetry in Heqres.
      pose proof VMEM_REF.mmodu_refine _ _ _ _ _ V1 V2 Heqres
        as (?&?&?).
      setoid_rewrite H.
      rewrite H0 in Heqo.
      rewrite IS1.LP.IP.to_Z_from_Z in Heqo.
      inv Heqo.
      auto.
    - (* SRem *)
      cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL.
      setoid_rewrite dtyp_eqb_refl in EVAL.
      inv EVAL.
    - (* And *)
      cbn in *; inv EVAL.
      remember (mand v1_fin v2_fin) as res_fin.
      symmetry in Heqres_fin.

      epose proof VMEM_REF.mand_refine _ _ _ v1_inf v2_inf V1 V2 Heqres_fin as (?&?&?).
      setoid_rewrite H; cbn in *.

      break_match_hyp_inv.
      rewrite H0 in Heqo.
      rewrite IS1.LP.IP.to_Z_from_Z in Heqo.
      inv Heqo.
      reflexivity.
    - (* Or *)
      cbn in *; inv EVAL.
      remember (mor v1_fin v2_fin) as res_fin.
      symmetry in Heqres_fin.

      epose proof VMEM_REF.mor_refine _ _ _ v1_inf v2_inf V1 V2 Heqres_fin as (?&?&?).
      setoid_rewrite H; cbn in *.

      break_match_hyp_inv.
      rewrite H0 in Heqo.
      rewrite IS1.LP.IP.to_Z_from_Z in Heqo.
      inv Heqo.
      reflexivity.
    - (* Xor *)
      cbn in *; inv EVAL.
      remember (mxor v1_fin v2_fin) as res_fin.
      symmetry in Heqres_fin.

      epose proof VMEM_REF.mxor_refine _ _ _ v1_inf v2_inf V1 V2 Heqres_fin as (?&?&?).
      setoid_rewrite H; cbn in *.

      break_match_hyp_inv.
      rewrite H0 in Heqo.
      rewrite IS1.LP.IP.to_Z_from_Z in Heqo.
      inv Heqo.
      reflexivity.
  Qed.

  Lemma dvalue_convert_strict_fin_inf_succeeds_fin_to_inf_dvalue' :
    forall res,
      DVCrev.dvalue_convert_strict res = NoOom (fin_to_inf_dvalue res).
  Proof.
    intros res.
    unfold fin_to_inf_dvalue.
    break_match_goal.
    destruct p.
    clear Heqs.
    auto.
  Qed.

  Hint Resolve
    eval_int_op_ix_fin_inf
    eval_int_op_iptr_fin_inf
    dvalue_convert_strict_fin_inf_succeeds_fin_to_inf_dvalue'
    : EVAL_INT_FIN_INF.

  (* TODO: Move this / generalize monad? *)
  Lemma eval_iop_integer_h_fin_inf :
    forall dv1_fin dv2_fin res_fin iop dv1_inf dv2_inf,
      @eval_iop_integer_h err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        iop dv1_fin dv2_fin = ret res_fin ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @IS1.LP.Events.DV.eval_iop_integer_h err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        iop dv1_inf dv2_inf = ret (fin_to_inf_dvalue res_fin).
  Proof.
    intros dv1_fin dv2_fin res_fin iop dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    unfold eval_iop_integer_h in EVAL.
    (* Nasty case analysis... *)
    repeat break_match_hyp_inv;
      rewrite_fin_to_inf_dvalue;
      cbn in *;
      try setoid_rewrite Heqb; cbn; eauto with EVAL_INT_FIN_INF.

    { (* dv1: ix *)
      break_match_goal; cbn in *; subst; try contradiction.
      dependent destruction e; cbn.
      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs.
      destruct p; clear e0.
      unfold intptr_fin_inf.
      repeat break_match_goal.
      eapply eval_int_op_ix_fin_inf; eauto.
    }

    { (* dv1: iptr *)
      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs.
      destruct p; clear e0.
      unfold intptr_fin_inf.
      repeat break_match_goal.
      clear Heqs Heqs0.
      eapply eval_int_op_iptr_fin_inf; eauto.
    }
  Qed.

  Hint Resolve eval_iop_integer_h_fin_inf : EVAL_INT_FIN_INF.

  (* TODO: Move this *)
  Lemma combine_cons :
    forall {X Y} (x : X) (y : Y) xs ys,
      combine (x :: xs) (y :: ys) = (x,y) :: combine xs ys.
  Proof.
    cbn; auto.
  Qed.

  (* TODO: Move this *)
  Lemma vec_loop_cons :
    forall {A M} `{HM : Monad M}
      (f : A -> A -> M A)
      a b xs,
      @vec_loop A M HM f ((a,b) :: xs) =
        res <- @vec_loop A M HM f xs;;
        val <- f a b;;
        ret (val :: res).
  Proof.
    intros A M HM f a b xs.
    cbn.
    reflexivity.
  Qed.

  Lemma vec_loop_fin_inf :
    forall f_fin f_inf xs ys res,
      (forall dv1_fin dv2_fin res_fin dv1_inf dv2_inf,
          f_fin dv1_fin dv2_fin = ret res_fin ->
          fin_to_inf_dvalue dv1_fin = dv1_inf ->
          fin_to_inf_dvalue dv2_fin = dv2_inf ->
          f_inf dv1_inf dv2_inf = ret (fin_to_inf_dvalue res_fin)) ->
      @vec_loop _ err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) f_fin (combine xs ys) = ret res ->
      @IS1.LP.Events.DV.vec_loop _ err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) f_inf (combine (map fin_to_inf_dvalue xs) (map fin_to_inf_dvalue ys)) = ret (map fin_to_inf_dvalue res).
  Proof.
    intros f_fin f_inf xs ys res F RES.

    remember (xs, ys) as ZIP.
    replace xs with (fst ZIP) by (subst; cbn; auto).
    replace ys with (snd ZIP) by (subst; cbn; auto).
    replace xs with (fst ZIP) in RES by (subst; cbn; auto).
    replace ys with (snd ZIP) in RES by (subst; cbn; auto).
    clear HeqZIP xs ys.

    generalize dependent res.
    induction ZIP using double_list_rect; intros res RES;
      try solve [cbn in *; inv RES; auto].
    - (* Both cons *)
      unfold fst, snd in *.
      repeat rewrite map_cons.
      repeat rewrite combine_cons.
      repeat rewrite vec_loop_cons.
      rewrite combine_cons in RES.
      rewrite vec_loop_cons in RES.
      cbn in RES.
      remember (vec_loop f_fin (combine xs ys)) as res'.
      destruct_err_ub_oom res';
        cbn in RES; inv RES.
      specialize (IHZIP _ eq_refl).
      cbn.
      (* Not sure why rewrite won't work... *)
      replace
        (@vec_loop DVCrev.DV2.dvalue err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) f_inf
           (@combine DVCrev.DV2.dvalue DVCrev.DV2.dvalue (@map DVCrev.DV1.dvalue DVCrev.DV2.dvalue fin_to_inf_dvalue xs)
              (@map DVCrev.DV1.dvalue DVCrev.DV2.dvalue fin_to_inf_dvalue ys)))
        with (@ret err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
                (list DVCrev.DV2.dvalue) (@map DVCrev.DV1.dvalue DVCrev.DV2.dvalue fin_to_inf_dvalue res'0)); cbn; eauto.

      remember (f_fin x y) as res_start.
      destruct_err_ub_oom res_start; inv H0.
      symmetry in Heqres_start.
      eapply F in Heqres_start; eauto.

      rewrite Heqres_start.
      cbn.
      reflexivity.
  Qed.

  (* TODO: Move this / generalize monad? *)
  Lemma eval_iop_fin_inf :
    forall dv1_fin dv2_fin res_fin iop dv1_inf dv2_inf,
      @eval_iop err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        iop dv1_fin dv2_fin = ret res_fin ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @IS1.LP.Events.DV.eval_iop err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        iop dv1_inf dv2_inf = ret (fin_to_inf_dvalue res_fin).
  Proof.
    intros dv1_fin dv2_fin res_fin iop dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    unfold eval_iop in EVAL.
    (* Nasty case analysis... *)
    repeat break_match_hyp_inv;
      rewrite_fin_to_inf_dvalue;
      cbn;
      try setoid_rewrite Heqb; eauto with EVAL_INT_FIN_INF.

    { (* dv1: ix *)
      unfold fin_to_inf_dvalue.
      break_match_goal; try contradiction.
      dependent destruction e.
      break_match_goal; clear Heqs.
      destruct p; clear e0.
      unfold intptr_fin_inf.
      repeat break_match_goal.
      eapply eval_int_op_ix_fin_inf; eauto.
    }

    { (* dv1: iptr *)
      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs.
      destruct p; clear e0.
      unfold intptr_fin_inf.
      repeat break_match_goal.
      clear Heqs Heqs0.
      eapply eval_int_op_iptr_fin_inf; eauto.
    }

    { (* dv1: Vector *)
      (* dv2 is also a vector *)
      remember (vec_loop (eval_iop_integer_h iop) (combine elts elts0)) as res.
      destruct_err_ub_oom res; cbn in *; inv Heqs; inv Heqe; inv H0.

      symmetry in Heqres.
      erewrite vec_loop_fin_inf; cbn; eauto.

      intros dv1_fin dv2_fin res_fin dv1_inf dv2_inf H H0 H1.
      eapply eval_iop_integer_h_fin_inf; eauto.
    }
  Qed.

  Hint Resolve eval_iop_fin_inf : EVAL_INT_FIN_INF.

  Lemma ptr_to_int_fin_to_inf_addr :
    forall a,
      IS1.LP.PTOI.ptr_to_int (fin_to_inf_addr a) = PTOI.ptr_to_int a.
  Proof.
    intros a.
    unfold fin_to_inf_addr.
    break_match_goal.
    clear Heqs.
    erewrite AC2.addr_convert_ptoi; eauto.
  Qed.

  Lemma eval_int_icmp_fin_inf :
    forall {Int} {VMInt : VellvmIntegers.VMemInt Int} icmp a b res_fin,
      @eval_int_icmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) Int VMInt icmp a b = ret res_fin  ->
      @IS1.LP.Events.DV.eval_int_icmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) Int VMInt icmp a b = ret (fin_to_inf_dvalue res_fin).
  Proof.
    intros Int VMInt icmp a b res_fin FIN.
    unfold eval_int_icmp, IS1.LP.Events.DV.eval_int_icmp.
    destruct icmp;
      try solve
        [ cbn in *;
          break_match_hyp_inv;
          rewrite_fin_to_inf_dvalue;
          eauto
        | cbn in *;
          repeat break_match_hyp_inv; inv Heqs;
          cbn;
          break_match_goal;
          rewrite_fin_to_inf_dvalue; auto
        ].
  Qed.

  (* TODO: Move this *)
  Lemma eval_int_icmp_iptr_fin_inf :
    forall v1_fin v2_fin v1_inf v2_inf icmp res_fin res_inf,
      @eval_int_icmp err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        IP.intptr
        VMemInt_intptr'
        icmp v1_fin v2_fin = success_unERR_UB_OOM res_fin ->
      IS1.LP.IP.from_Z (IP.to_Z v1_fin) = NoOom v1_inf ->
      IS1.LP.IP.from_Z (IP.to_Z v2_fin) = NoOom v2_inf ->
      DVCrev.dvalue_convert_strict res_fin = NoOom res_inf ->
      @IS1.LP.Events.DV.eval_int_icmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        IS1.LP.IP.intptr
        IS1.LP.Events.DV.VMemInt_intptr'
        icmp v1_inf v2_inf = success_unERR_UB_OOM res_inf.
  Proof.
    intros v1_fin v2_fin v1_inf v2_inf icmp res_fin res_inf EVAL LIFT1 LIFT2 CONV.

    assert (IP.to_Z v1_fin = IS1.LP.IP.to_Z v1_inf) as V1.
    { erewrite IS1.LP.IP.from_Z_to_Z; eauto. }

    assert (IP.to_Z v2_fin = IS1.LP.IP.to_Z v2_inf) as V2.
    { erewrite IS1.LP.IP.from_Z_to_Z; eauto. }

    destruct icmp;
      try
        solve
        [ cbn in *;
          erewrite <- VMEM_REF.mcmpu_refine; eauto;
          break_match_hyp_inv;
          setoid_rewrite Heqb;
          cbn in CONV; inv CONV; auto
        | cbn in *;
          setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL;
          setoid_rewrite dtyp_eqb_refl in EVAL;
          inv EVAL
        ].
  Qed.

  (* TODO: Move this / generalize monad? *)
  Lemma eval_icmp_fin_inf :
    forall dv1_fin dv2_fin res_fin icmp dv1_inf dv2_inf,
      @eval_icmp err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        icmp dv1_fin dv2_fin = ret res_fin ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @IS1.MEM.CP.CONC.eval_icmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        icmp dv1_inf dv2_inf = ret (fin_to_inf_dvalue res_fin).
  Proof.
    intros dv1_fin dv2_fin res_fin icmp dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    Opaque IS1.LP.Events.DV.eval_int_icmp
      eval_int_icmp.
    unfold eval_icmp in EVAL.
    (* Nasty case analysis... *)
    break_match_hyp_inv;
      try solve
        [ (* Simple integer cases *)
          break_match_hyp_inv;
          repeat rewrite_fin_to_inf_dvalue;
          cbn;
          auto;
          eapply eval_int_icmp_fin_inf in H1;
          auto
        ].

    { (* dv1: addr *)
      break_match_hyp_inv.
      repeat rewrite_fin_to_inf_dvalue.
      cbn.
      eapply eval_int_icmp_fin_inf in H1.
      repeat rewrite ptr_to_int_fin_to_inf_addr.
      auto.
    }

    { (* dv1: ix *)
      break_match_hyp_inv.
      - break_match_hyp_inv; try contradiction; cbn in *; subst.
        repeat rewrite_fin_to_inf_dvalue.
        cbn.
        unfold intptr_fin_inf.
        eapply eval_int_icmp_fin_inf in H0; eauto.
        unfold IS1.MEM.CP.CONC.eval_icmp.
        break_match_goal; try contradiction.
        dependent destruction e; cbn; auto.
      - repeat rewrite_fin_to_inf_dvalue.
        cbn.
        unfold intptr_fin_inf; auto.
    }

    { (* dv1: iptr *)
      break_match_hyp_inv.
      repeat rewrite_fin_to_inf_dvalue.
      cbn.
      unfold intptr_fin_inf.
      do 2 break_match_goal.
      clear Heqs Heqs0.
      eapply eval_int_icmp_iptr_fin_inf in H1; eauto.
      eapply dvalue_convert_strict_fin_inf_succeeds_fin_to_inf_dvalue'.
    }
  Qed.

  Lemma double_op_fin_inf :
    forall fop a b res_fin res_inf,
      double_op fop a b = success_unERR_UB_OOM res_fin ->
      DVCrev.dvalue_convert_strict res_fin = NoOom res_inf ->
      IS1.LP.Events.DV.double_op fop a b = success_unERR_UB_OOM res_inf.
  Proof.
    intros fop a b res_fin res_inf EVAL REF.
    destruct fop; cbn in *; inv EVAL;
      cbn in REF;
      inv REF; reflexivity.
  Qed.

  Lemma float_op_fin_inf :
    forall fop a b res_fin res_inf,
      float_op fop a b = success_unERR_UB_OOM res_fin ->
      DVCrev.dvalue_convert_strict res_fin = NoOom res_inf ->
      IS1.LP.Events.DV.float_op fop a b = success_unERR_UB_OOM res_inf.
  Proof.
    intros fop a b res_fin res_inf EVAL REF.
    destruct fop; cbn in *; inv EVAL;
      cbn in REF;
      inv REF; reflexivity.
  Qed.

  (* TODO: Move this / generalize monad? *)
  Lemma eval_fop_fin_inf :
    forall dv1_fin dv2_fin res_fin fop dv1_inf dv2_inf,
      @eval_fop err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        fop dv1_fin dv2_fin = ret res_fin ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @IS1.LP.Events.DV.eval_fop err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        fop dv1_inf dv2_inf = ret (fin_to_inf_dvalue res_fin).
  Proof.
    intros dv1_fin dv2_fin res_fin fop dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    unfold eval_fop in EVAL.
    (* Nasty case analysis... *)
    break_match_hyp_inv.
    { (* dv1: Double *)
      break_match_hyp_inv.
      2: {
        break_match_hyp_inv.
        unfold fin_to_inf_dvalue.
        break_match_goal; clear Heqs; destruct p; clear e0.
        break_match_goal; clear Heqs; destruct p; clear e1.
        inv e; inv e0.
        cbn.

        (* These should be the same... *)
        unfold IS1.LP.Events.DV.fop_is_div.
        unfold fop_is_div in Heqb.
        rewrite Heqb.
        reflexivity.
      }

      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs; destruct p; clear e0.
      break_match_goal; clear Heqs; destruct p; clear e1.
      inv e; inv e0.
      cbn.
      break_match_goal; clear Heqs; destruct p; clear e0.
      eapply double_op_fin_inf; eauto.
    }

    { (* dv1: Float *)
      break_match_hyp_inv.
      2: {
        break_match_hyp_inv.
        unfold fin_to_inf_dvalue.
        break_match_goal; clear Heqs; destruct p; clear e0.
        break_match_goal; clear Heqs; destruct p; clear e1.
        inv e; inv e0.
        cbn.

        (* These should be the same... *)
        unfold IS1.LP.Events.DV.fop_is_div.
        unfold fop_is_div in Heqb.
        rewrite Heqb.
        reflexivity.
      }

      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs; destruct p; clear e0.
      break_match_goal; clear Heqs; destruct p; clear e1.
      inv e; inv e0.
      cbn.
      break_match_goal; clear Heqs; destruct p; clear e0.
      eapply float_op_fin_inf; eauto.
    }

    { (* dv1: Poison *)
      unfold fin_to_inf_dvalue.

      break_match_goal; clear Heqs; destruct p; clear e0;
        cbn in *; inv e.
      cbn. reflexivity.
    }
  Qed.

  Lemma double_cmp_fin_inf :
    forall fcmp a b res_fin res_inf,
      double_cmp fcmp a b = res_fin ->
      DVCrev.dvalue_convert_strict res_fin = NoOom res_inf ->
      IS1.LP.Events.DV.double_cmp fcmp a b = res_inf.
  Proof.
    intros fcmp a b res_fin res_inf EVAL REF.
    destruct fcmp; cbn in *; subst;
      cbn in REF;
      inv REF; auto;
      solve
        [ unfold double_cmp, IS1.LP.Events.DV.double_cmp in *;
          repeat break_match_hyp_inv; auto;
          setoid_rewrite Heqb0; reflexivity
        ].
  Qed.

  Lemma float_cmp_fin_inf :
    forall fcmp a b res_fin res_inf,
      float_cmp fcmp a b = res_fin ->
      DVCrev.dvalue_convert_strict res_fin = NoOom res_inf ->
      IS1.LP.Events.DV.float_cmp fcmp a b = res_inf.
  Proof.
    intros fcmp a b res_fin res_inf EVAL REF.
    destruct fcmp; cbn in *; subst;
      cbn in REF;
      inv REF; auto;
      solve
        [ unfold float_cmp, IS1.LP.Events.DV.float_cmp in *;
          repeat break_match_hyp_inv; auto;
          setoid_rewrite Heqb0; reflexivity
        ].
  Qed.

  (* TODO: Move this / generalize monad? *)
  Lemma eval_fcmp_fin_inf :
    forall dv1_fin dv2_fin res_fin fcmp dv1_inf dv2_inf,
      @eval_fcmp err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        fcmp dv1_fin dv2_fin = ret res_fin ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @IS1.LP.Events.DV.eval_fcmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        fcmp dv1_inf dv2_inf = ret (fin_to_inf_dvalue res_fin).
  Proof.
    intros dv1_fin dv2_fin res_fin fcmp dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    unfold eval_fcmp in EVAL.
    (* Nasty case analysis... *)
    break_match_hyp_inv;
      try solve
        [ (* Simple integer cases *)
          break_match_hyp_inv;
          [ unfold fin_to_inf_dvalue;

            break_match_goal; clear Heqs; destruct p; clear e0;
            cbn in *; inv e;

            break_match_goal; clear Heqs; destruct p; clear e0;
            cbn in *; inv e;

            break_match_goal; clear Heqs; destruct p; clear e0;
            cbn;

            rewrite eval_int_icmp_fin_inf in e; inv e;
            reflexivity
          | unfold fin_to_inf_dvalue;

            break_match_goal; clear Heqs; destruct p; clear e0;
            cbn in *; inv e;

            break_match_goal; clear Heqs; destruct p; clear e0;
            cbn in *; inv e;

            cbn;
            reflexivity
          ]
        | (* Ill-typed cases *)
          break_match_hyp_inv
        ].

    { (* dv1: Double *)
      break_match_hyp_inv.
      unfold fin_to_inf_dvalue.

      break_match_goal; clear Heqs; destruct p; clear e0.
      cbn in *; inv e.

      break_match_goal; clear Heqs; destruct p; clear e0.
      cbn in *; inv e.

      break_match_goal; clear Heqs; destruct p; clear e0.
      cbn.

      erewrite double_cmp_fin_inf; eauto.
      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs; destruct p; clear e0.
      cbn in *; inv e.

      break_match_goal; clear Heqs; destruct p; clear e0.
      cbn in *; inv e.
      reflexivity.
    }

    { (* dv1: Float *)
      break_match_hyp_inv.
      unfold fin_to_inf_dvalue.

      break_match_goal; clear Heqs; destruct p; clear e0.
      cbn in *; inv e.

      break_match_goal; clear Heqs; destruct p; clear e0.
      cbn in *; inv e.

      break_match_goal; clear Heqs; destruct p; clear e0.
      cbn.

      erewrite float_cmp_fin_inf; eauto.
      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs; destruct p; clear e0.
      cbn in *; inv e.

      break_match_goal; clear Heqs; destruct p; clear e0.
      cbn in *; inv e.
      reflexivity.
    }

    { (* dv1: poison *)
      break_match_hyp_inv;
        unfold fin_to_inf_dvalue;

        break_match_goal; clear Heqs; destruct p; clear e0;
        cbn in *; inv e;

        break_match_goal; clear Heqs; destruct p; clear e0;
        cbn in *; inv e;

        cbn;
        reflexivity.
    }
  Qed.

  Definition dvalue_byte_refine
    (dvb_inf : IS1.MEM.DVALUE_BYTE.dvalue_byte)
    (dvb_fin : dvalue_byte) : Prop
    :=
    match dvb_inf, dvb_fin with
    | (IS1.MEM.DVALUE_BYTE.DVALUE_ExtractByte dv_inf dt_inf ix_inf),
      (DVALUE_ExtractByte dv_fin dt_fin ix_fin)
      =>
        dvalue_refine_strict dv_inf dv_fin /\
          dt_inf = dt_fin /\
          ix_inf = ix_fin
    end.

  Definition inf_to_fin_dvalue_byte
    (dvb_inf : IS1.MEM.DVALUE_BYTE.dvalue_byte) : OOM dvalue_byte
    :=
    match dvb_inf with
    | (IS1.MEM.DVALUE_BYTE.DVALUE_ExtractByte dv_inf dt ix)
      =>
        dv_fin <- dvalue_convert_strict dv_inf;;
        ret (DVALUE_ExtractByte dv_fin dt ix)
    end.

  Definition fin_to_inf_dvalue_byte
    (dvb_fin : dvalue_byte) : IS1.MEM.DVALUE_BYTE.dvalue_byte
    :=
    match dvb_fin with
    | DVALUE_ExtractByte dv_fin dt ix
      =>
        let dv_inf := fin_to_inf_dvalue dv_fin in
        IS1.MEM.DVALUE_BYTE.DVALUE_ExtractByte dv_inf dt ix
    end.

  Definition dvalue_bytes_refine
    (dvbs_inf : list IS1.MEM.DVALUE_BYTE.dvalue_byte)
    (dvbs_fin : list dvalue_byte) : Prop
    := Forall2 dvalue_byte_refine dvbs_inf dvbs_fin.

  Definition fin_to_inf_dvalue_bytes := map fin_to_inf_dvalue_byte.

  Lemma dvalue_byte_refine_fin_to_inf_dvalue_byte :
    forall a,
      dvalue_byte_refine (fin_to_inf_dvalue_byte a) a.
  Proof.
    intros a.
    red.
    repeat break_match_goal; subst.
    cbn in Heqd.
    inv Heqd.
    split; auto.
    apply fin_to_inf_dvalue_refine_strict.
  Qed.

  Lemma dvalue_bytes_refine_fin_to_inf_dvalue_bytes :
    forall dvs,
      dvalue_bytes_refine (fin_to_inf_dvalue_bytes dvs) dvs.
  Proof.
    induction dvs; cbn; auto.
    - constructor.
    - constructor; auto.
      apply dvalue_byte_refine_fin_to_inf_dvalue_byte.
  Qed.

  Lemma dvalue_to_dvalue_bytes_fin_inf :
    forall dv_fin dv_inf dt dvbs_fin,
      dvalue_refine_strict dv_inf dv_fin ->
      DVALUE_BYTE.dvalue_to_dvalue_bytes dv_fin dt = dvbs_fin ->
      IS1.MEM.DVALUE_BYTE.dvalue_to_dvalue_bytes dv_inf dt = fin_to_inf_dvalue_bytes dvbs_fin.
  Proof.
    intros dv_fin dv_inf dt dvbs_fin DV_REF DV_DVBS.
    unfold dvalue_to_dvalue_bytes in DV_DVBS.
    unfold IS1.MEM.DVALUE_BYTE.dvalue_to_dvalue_bytes.
    rewrite sizeof_dtyp_fin_inf.
    subst.
    unfold fin_to_inf_dvalue_bytes.
    rewrite List.map_map.
    cbn.
    erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
  Qed.

  Lemma all_extract_bytes_from_uvalue_helper_fin_inf :
    forall uv_bytes_inf uv_bytes_fin uv_inf uv_fin ix sid dt,
      uvalue_refine_strict uv_inf uv_fin ->
      map_monad uvalue_convert_strict uv_bytes_inf = NoOom uv_bytes_fin ->
      IS1.MEM.ByteM.all_extract_bytes_from_uvalue_helper ix sid dt uv_inf uv_bytes_inf =
        fmap fin_to_inf_uvalue (all_extract_bytes_from_uvalue_helper ix sid dt uv_fin uv_bytes_fin).
  Proof.
    induction uv_bytes_inf;
      intros uv_bytes_fin uv_inf uv_fin ix sid dt UV_REF HMAPM.
    - inv HMAPM.
      cbn.
      erewrite <- fin_to_inf_uvalue_refine_strict'; eauto.
    - cbn in HMAPM.
      repeat break_match_hyp_inv.
      cbn.
      erewrite IHuv_bytes_inf; eauto.

      destruct a; cbn in Heqo;
        repeat break_match_hyp_inv; try inv Heqo; auto.

      unfold IS1.LLVM.MEM.CP.CONCBASE.MemHelpers.dtyp_eqb, MemHelpers.dtyp_eqb.
      repeat rewrite Util.eq_dec_eq; cbn.
      repeat rewrite N.eqb_refl; cbn.
      repeat (break_inner_match; subst; cbn; auto).
      + destruct (RelDec.rel_dec a uv_inf) eqn:UV_INF; inv Heqo2.
        assert (a = uv_inf) as AUV_INF.
        { eapply RelDec.rel_dec_correct; eauto. }
        subst.
        rewrite UV_REF in Heqo1. inv Heqo1.
        rewrite Util.eq_dec_eq in Heqo6.
        inv Heqo6.
      + destruct (RelDec.rel_dec u0 uv_fin) eqn:UV_FIN; inv Heqo3.
        assert (u0 = uv_fin) as AUV_FIN.
        { eapply RelDec.rel_dec_correct; eauto. }
        subst.

        pose proof uvalue_refine_strict_R2_injective _ _ _ _ UV_REF Heqo1 as (_&?).
        forward H; auto; subst.
        rewrite UV_REF in Heqo1. inv Heqo1.
        rewrite Util.eq_dec_eq in Heqo2; inv Heqo2.
  Qed.

  Lemma all_extract_bytes_from_uvalue_fin_inf :
    forall uv_bytes_inf uv_bytes_fin dt,
      map_monad uvalue_convert_strict uv_bytes_inf = NoOom uv_bytes_fin ->
      IS1.MEM.ByteM.all_extract_bytes_from_uvalue dt uv_bytes_inf =
        fmap fin_to_inf_uvalue (all_extract_bytes_from_uvalue dt uv_bytes_fin).
  Proof.
    intros uv_bytes_inf uv_bytes_fin dt HMAPM.
    unfold IS1.MEM.ByteM.all_extract_bytes_from_uvalue,
      all_extract_bytes_from_uvalue.

    destruct uv_bytes_inf.
    - cbn in HMAPM; inv HMAPM.
      cbn; auto.
    - rewrite map_monad_unfold in HMAPM.
      cbn in HMAPM.
      repeat break_match_hyp_inv.
      destruct u; cbn in Heqo;
        repeat break_match_hyp_inv; try inv Heqo; auto.

      cbn.
      unfold IS1.LLVM.MEM.CP.CONCBASE.MemHelpers.dtyp_eqb, MemHelpers.dtyp_eqb.
      repeat rewrite Util.eq_dec_eq; cbn.
      repeat rewrite N.eqb_refl; cbn.
      do 3 (break_inner_match; subst; cbn; auto).
      erewrite all_extract_bytes_from_uvalue_helper_fin_inf; eauto.
      reflexivity.
  Qed.

  Lemma uvalue_direct_subterm_fin_inf :
    forall u_fin uv_fin u_inf uv_inf,
      uvalue_refine_strict u_inf u_fin ->
      uvalue_refine_strict uv_inf uv_fin ->
      DV2.uvalue_direct_subterm u_fin uv_fin ->
      DV1.uvalue_direct_subterm u_inf uv_inf.
  Proof.
    intros u_fin uv_fin u_inf uv_inf REF_U REF_UV SUB.
    revert u_fin u_inf REF_U SUB.
    induction uv_inf using DV1.uvalue_strong_ind;
      intros u_fin u_inf REF_U SUB;
      try
        solve
        [ repeat red in REF_UV; cbn in REF_UV;
          try break_match_hyp_inv;
          try inv REF_UV;
          inv SUB
        ].

    inv SUB;
      DVC.uvalue_refine_strict_inv REF_UV;
      try
        solve
        [ (* Struct cases *)
          constructor;
          match goal with
          | H : map_monad uvalue_convert_strict _ = NoOom ?fields,
              HIN : In _ ?fields |-
              _ =>
              apply map_monad_oom_Forall2 in H;
              pose proof Forall2_In_exists2 _ _ _ _ H HIN as (?&?&CONV_u_fin);
              red in REF_U;
              pose proof uvalue_refine_strict_R2_injective _ _ _ _ REF_U CONV_u_fin as (_&INJ);
              forward INJ; subst; auto
          end
        | (* Binop cases *)
          match goal with
          | H2 : uvalue_convert_strict _ = NoOom ?u_fin,
              REF_U : uvalue_refine_strict _ ?u_fin |-
              _ =>
              pose proof uvalue_refine_strict_R2_injective _ _ _ _ REF_U H2 as (_&INJ);
              forward INJ; subst; auto;
              constructor
          end
        ].
  Qed.

  Lemma uvalue_strict_subterm_fin_inf :
    forall u_fin uv_fin u_inf uv_inf,
      uvalue_refine_strict u_inf u_fin ->
      uvalue_refine_strict uv_inf uv_fin ->
      DV2.uvalue_strict_subterm u_fin uv_fin ->
      DV1.uvalue_strict_subterm u_inf uv_inf.
  Proof.
    intros u_fin uv_fin u_inf uv_inf H H0 H1.
    eapply clos_trans_t1n_iff.
    revert u_inf uv_inf H H0.
    eapply clos_trans_t1n_iff in H1.
    induction H1; intros u_inf uv_inf H' H0.
    - apply t1n_step.
      eapply uvalue_direct_subterm_fin_inf; eauto.
    - eapply Relation_Operators.t1n_trans with (y:=fin_to_inf_uvalue y).
      + eapply uvalue_direct_subterm_fin_inf; eauto.
        apply convert_fin_to_inf_uvalue_succeeds.
      + eapply IHclos_trans_1n; auto.
        apply convert_fin_to_inf_uvalue_succeeds.
  Qed.

  Lemma extract_field_byte_helper_fin_inf :
    forall {M : Type -> Type} {HM: Monad M} {RE: RAISE_ERROR M}
      (field_dts : list dtyp) (field_idx : N) (byte_idx : N),
      @IS1.LLVM.MEM.DVALUE_BYTE.extract_field_byte_helper M HM RE field_dts field_idx byte_idx =
        @extract_field_byte_helper M HM RE field_dts field_idx byte_idx.
  Proof.
    intros M HM RE field_dts.
    induction field_dts;
      intros field_idx byte_idx;
      cbn; auto.
    rewrite sizeof_dtyp_fin_inf.
    rewrite IHfield_dts.
    reflexivity.
  Qed.

  Lemma extract_field_byte_fin_inf :
    forall {M : Type -> Type} {HM: Monad M} {RE: RAISE_ERROR M}
      (field_dts : list dtyp) (byte_idx : N),
      @IS1.LLVM.MEM.DVALUE_BYTE.extract_field_byte M HM RE field_dts byte_idx =
        @extract_field_byte M HM RE field_dts byte_idx.
  Proof.
    intros M HM RE field_dts byte_idx.
    apply extract_field_byte_helper_fin_inf.
  Qed.

  (* TODO: Move this and use this *)
  Ltac destruct_err_oom_poison x :=
    destruct x as [[[[[?err_x | ?x] | ?oom_x] | ?poison_x]]] eqn:?Hx.

  Lemma dvalue_extract_byte_fin_inf :
    forall dv_fin dv_inf dt idx,
      dvalue_refine_strict dv_inf dv_fin ->
      @dvalue_extract_byte ErrOOMPoison
        (@EitherMonad.Monad_eitherT ERR_MESSAGE (OomableT Poisonable)
           (@Monad_OomableT Poisonable MonadPoisonable))
        (@RAISE_ERROR_MonadExc ErrOOMPoison
           (@EitherMonad.Exception_eitherT ERR_MESSAGE (OomableT Poisonable)
              (@Monad_OomableT Poisonable MonadPoisonable)))
        (@RAISE_POISON_E_MT (OomableT Poisonable) (EitherMonad.eitherT ERR_MESSAGE)
           (@EitherMonad.MonadT_eitherT ERR_MESSAGE (OomableT Poisonable)
              (@Monad_OomableT Poisonable MonadPoisonable))
           (@RAISE_POISON_E_MT Poisonable OomableT (@MonadT_OomableT Poisonable MonadPoisonable)
              RAISE_POISON_Poisonable))
        (@RAISE_OOMABLE_E_MT (OomableT Poisonable) (EitherMonad.eitherT ERR_MESSAGE)
           (@EitherMonad.MonadT_eitherT ERR_MESSAGE (OomableT Poisonable)
              (@Monad_OomableT Poisonable MonadPoisonable))
           (@RAISE_OOMABLE_OomableT Poisonable MonadPoisonable)) dv_fin dt idx =
        @IS1.LLVM.MEM.DVALUE_BYTE.dvalue_extract_byte ErrOOMPoison
          (@EitherMonad.Monad_eitherT ERR_MESSAGE (OomableT Poisonable)
             (@Monad_OomableT Poisonable MonadPoisonable))
          (@RAISE_ERROR_MonadExc ErrOOMPoison
             (@EitherMonad.Exception_eitherT ERR_MESSAGE (OomableT Poisonable)
                (@Monad_OomableT Poisonable MonadPoisonable)))
          (@RAISE_POISON_E_MT (OomableT Poisonable) (EitherMonad.eitherT ERR_MESSAGE)
             (@EitherMonad.MonadT_eitherT ERR_MESSAGE (OomableT Poisonable)
                (@Monad_OomableT Poisonable MonadPoisonable))
             (@RAISE_POISON_E_MT Poisonable OomableT (@MonadT_OomableT Poisonable MonadPoisonable)
                RAISE_POISON_Poisonable))
          (@RAISE_OOMABLE_E_MT (OomableT Poisonable) (EitherMonad.eitherT ERR_MESSAGE)
             (@EitherMonad.MonadT_eitherT ERR_MESSAGE (OomableT Poisonable)
                (@Monad_OomableT Poisonable MonadPoisonable))
             (@RAISE_OOMABLE_OomableT Poisonable MonadPoisonable)) dv_inf dt idx.
  Proof.
    Opaque dvalue_extract_byte.
    Opaque IS1.LLVM.MEM.DVALUE_BYTE.dvalue_extract_byte.
    induction dv_fin;
      intros dv_inf dt idx REF;
      rewrite dvalue_extract_byte_equation,
      IS1.LLVM.MEM.DVALUE_BYTE.dvalue_extract_byte_equation;
      try solve
        [ dvalue_refine_strict_inv REF;
          unfold extract_byte_Z in *;
          try inv VAL;
          solve
            [ reflexivity
            | erewrite AC1.addr_convert_ptoi; eauto
            | erewrite IP.from_Z_to_Z; eauto
            ]
        ].
    
    (* - destruct dv_fin; *)
    (*     try solve *)
    (*       [ dvalue_refine_strict_inv REF; *)
    (*         unfold extract_byte_Z in *; *)
    (*         try inv H0; *)
    (*         solve *)
    (*           [ reflexivity *)
    (*           | erewrite AC1.addr_convert_ptoi; eauto *)
    (*           | erewrite IP.from_Z_to_Z; eauto *)
    (*           ] *)
    (*       ]. *)

      { (* Structs *)
        destruct dt;
        dvalue_refine_strict_inv REF; auto.
        rename fields0 into dts.
        rewrite max_preferred_dtyp_alignment_fin_inf.
        generalize (SIZEOF.max_preferred_dtyp_alignment dts) as struct_padding.
        revert dts idx.
        eapply map_monad_oom_Forall2 in H1.
        revert x H1.
        generalize 0 at 3 6 as offset.
        induction fields; intros; inversion H1; subst.
        - cbn. reflexivity.
        - destruct dts; try reflexivity.
          cbn.
          rewrite sizeof_dtyp_fin_inf.
          rewrite dtyp_alignment_fin_inf.
          break_match; try reflexivity.
          break_match.
          + apply H; cbn; auto.
          + forward IHfields; intros; auto.
            apply H; cbn; auto.
            cbn in IHfields.
            specialize (IHfields (offset + pad_amount (preferred_alignment (SIZEOF.dtyp_alignment d)) offset + SIZEOF.sizeof_dtyp d) l H5 dts (idx - Z.of_N (pad_amount (preferred_alignment (SIZEOF.dtyp_alignment d)) offset) - Z.of_N (SIZEOF.sizeof_dtyp d))%Z struct_padding).
            cbn in *.
            erewrite IHfields; intros; eauto.
      } 

      { (* Packed Structs *)
        destruct dt;
        dvalue_refine_strict_inv REF; auto.
        rename fields0 into dts.
        revert dts idx.
        eapply map_monad_oom_Forall2 in H1.
        revert x H1.
        generalize 0 at 3 6 as offset.
        induction fields; intros; inversion H1; subst.
        - reflexivity.
        - destruct dts; try reflexivity.
          cbn.
          rewrite sizeof_dtyp_fin_inf.
          break_match; try reflexivity.
          break_match.
          + apply H. repeat constructor. apply H4.
          + erewrite IHfields; intros; eauto. 
            apply H; auto.
            right. assumption.
      }

      { (* Arrays *)
        destruct dt;
        dvalue_refine_strict_inv REF; auto.
        revert idx.
        eapply map_monad_oom_Forall2 in H1.
        revert x H1.
        induction elts; intros; inversion H1; subst.
        - reflexivity.
        - cbn.
          rewrite sizeof_dtyp_fin_inf.
          destruct (idx <? Z.of_N (SIZEOF.sizeof_dtyp dt))%Z.
          + apply H. repeat constructor. apply H4.
          + erewrite IHelts; intros; eauto.
            apply H; cbn; auto.
      }

      { (* Vectors *)
        destruct dt;
        dvalue_refine_strict_inv REF; auto.
        revert idx.
        eapply map_monad_oom_Forall2 in H1.
        revert x H1.
        induction elts; intros; inversion H1; subst.
        - reflexivity.
        - cbn.
          rewrite sizeof_dtyp_fin_inf.
          destruct (idx <? Z.of_N (SIZEOF.sizeof_dtyp dt))%Z.
          + apply H. repeat constructor. apply H4.
          + apply IHelts; intros; auto.
            apply H; auto.
            right. assumption.
      }
  Qed.

  Lemma dvalue_byte_value_fin_inf :
    forall dvb_inf dvb_fin,
      dvalue_byte_refine dvb_inf dvb_fin ->
      @dvalue_byte_value ErrOOMPoison
        (@EitherMonad.Monad_eitherT ERR_MESSAGE (OomableT Poisonable)
           (@Monad_OomableT Poisonable MonadPoisonable))
        (@RAISE_ERROR_MonadExc ErrOOMPoison
           (@EitherMonad.Exception_eitherT ERR_MESSAGE (OomableT Poisonable)
              (@Monad_OomableT Poisonable MonadPoisonable)))
        (@RAISE_POISON_E_MT (OomableT Poisonable) (EitherMonad.eitherT ERR_MESSAGE)
           (@EitherMonad.MonadT_eitherT ERR_MESSAGE (OomableT Poisonable)
              (@Monad_OomableT Poisonable MonadPoisonable))
           (@RAISE_POISON_E_MT Poisonable OomableT (@MonadT_OomableT Poisonable MonadPoisonable)
              RAISE_POISON_Poisonable))
        (@RAISE_OOMABLE_E_MT (OomableT Poisonable) (EitherMonad.eitherT ERR_MESSAGE)
           (@EitherMonad.MonadT_eitherT ERR_MESSAGE (OomableT Poisonable)
              (@Monad_OomableT Poisonable MonadPoisonable))
           (@RAISE_OOMABLE_OomableT Poisonable MonadPoisonable)) dvb_fin =
      (@IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte_value ErrOOMPoison
         (@EitherMonad.Monad_eitherT ERR_MESSAGE
            (OomableT Poisonable)
            (@Monad_OomableT Poisonable
               MonadPoisonable))
         (@RAISE_ERROR_MonadExc ErrOOMPoison
            (@EitherMonad.Exception_eitherT ERR_MESSAGE
               (OomableT Poisonable)
               (@Monad_OomableT Poisonable
                  MonadPoisonable)))
         (@RAISE_POISON_E_MT
            (OomableT Poisonable)
            (EitherMonad.eitherT ERR_MESSAGE)
            (@EitherMonad.MonadT_eitherT ERR_MESSAGE
               (OomableT Poisonable)
               (@Monad_OomableT Poisonable
                  MonadPoisonable))
            (@RAISE_POISON_E_MT Poisonable
               OomableT
               (@MonadT_OomableT Poisonable
                  MonadPoisonable)
               RAISE_POISON_Poisonable))
         (@RAISE_OOMABLE_E_MT
            (OomableT Poisonable)
            (EitherMonad.eitherT ERR_MESSAGE)
            (@EitherMonad.MonadT_eitherT ERR_MESSAGE
               (OomableT Poisonable)
               (@Monad_OomableT Poisonable
                  MonadPoisonable))
            (@RAISE_OOMABLE_OomableT Poisonable
               MonadPoisonable))) dvb_inf.
  Proof.
    intros dvb_inf dvb_fin REF.
    unfold dvalue_byte_value.
    break_match; subst.
    unfold IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte_value.
    break_match_goal; subst.
    red in REF.
    destruct REF as (?&?&?).
    subst.
    eapply dvalue_extract_byte_fin_inf; eauto.
  Qed.

  Lemma map_monad_dvalue_byte_value_fin_inf :
    forall dvbs_inf dvbs_fin,
      dvalue_bytes_refine dvbs_inf dvbs_fin ->
      map_monad (@dvalue_byte_value ErrOOMPoison
        (@EitherMonad.Monad_eitherT ERR_MESSAGE (OomableT Poisonable)
           (@Monad_OomableT Poisonable MonadPoisonable))
        (@RAISE_ERROR_MonadExc ErrOOMPoison
           (@EitherMonad.Exception_eitherT ERR_MESSAGE (OomableT Poisonable)
              (@Monad_OomableT Poisonable MonadPoisonable)))
        (@RAISE_POISON_E_MT (OomableT Poisonable) (EitherMonad.eitherT ERR_MESSAGE)
           (@EitherMonad.MonadT_eitherT ERR_MESSAGE (OomableT Poisonable)
              (@Monad_OomableT Poisonable MonadPoisonable))
           (@RAISE_POISON_E_MT Poisonable OomableT (@MonadT_OomableT Poisonable MonadPoisonable)
              RAISE_POISON_Poisonable))
        (@RAISE_OOMABLE_E_MT (OomableT Poisonable) (EitherMonad.eitherT ERR_MESSAGE)
           (@EitherMonad.MonadT_eitherT ERR_MESSAGE (OomableT Poisonable)
              (@Monad_OomableT Poisonable MonadPoisonable))
           (@RAISE_OOMABLE_OomableT Poisonable MonadPoisonable))) dvbs_fin =
      map_monad (@IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte_value ErrOOMPoison
         (@EitherMonad.Monad_eitherT ERR_MESSAGE
            (OomableT Poisonable)
            (@Monad_OomableT Poisonable
               MonadPoisonable))
         (@RAISE_ERROR_MonadExc ErrOOMPoison
            (@EitherMonad.Exception_eitherT ERR_MESSAGE
               (OomableT Poisonable)
               (@Monad_OomableT Poisonable
                  MonadPoisonable)))
         (@RAISE_POISON_E_MT
            (OomableT Poisonable)
            (EitherMonad.eitherT ERR_MESSAGE)
            (@EitherMonad.MonadT_eitherT ERR_MESSAGE
               (OomableT Poisonable)
               (@Monad_OomableT Poisonable
                  MonadPoisonable))
            (@RAISE_POISON_E_MT Poisonable
               OomableT
               (@MonadT_OomableT Poisonable
                  MonadPoisonable)
               RAISE_POISON_Poisonable))
         (@RAISE_OOMABLE_E_MT
            (OomableT Poisonable)
            (EitherMonad.eitherT ERR_MESSAGE)
            (@EitherMonad.MonadT_eitherT ERR_MESSAGE
               (OomableT Poisonable)
               (@Monad_OomableT Poisonable
                  MonadPoisonable))
            (@RAISE_OOMABLE_OomableT Poisonable
               MonadPoisonable))) dvbs_inf.
  Proof.
    induction dvbs_inf;
      intros dvbs_fin REF.
    + inv REF.
      cbn in *; auto.
    + inv REF.
      rewrite map_monad_unfold.
      cbn.
      repeat erewrite dvalue_byte_value_fin_inf; eauto.
      rewrite IHdvbs_inf; eauto.
  Qed.

  Lemma ErrOOMPoison_bind_ret_inv :
    forall {A B} ma k res,
      @bind ErrOOMPoison
         (@EitherMonad.Monad_eitherT ERR_MESSAGE (OomableT Poisonable)
            (@Monad_OomableT Poisonable MonadPoisonable))
         A B
         ma k = ret res ->
      exists a, ma = ret a /\ k a = ret res.
  Proof.
    intros A B ma k res H.
    destruct ma, unEitherT, unMkOomableT; inv H.
    repeat break_match_hyp_inv.
    exists a.
    split; auto.
    destruct (k a), unEitherT, unMkOomableT; inv H1.
    reflexivity.
  Qed.

  Lemma ErrOOMPoison_bind_raise_poison_inv :
    forall {A B} ma k dt,
      @bind ErrOOMPoison
         (@EitherMonad.Monad_eitherT ERR_MESSAGE (OomableT Poisonable)
            (@Monad_OomableT Poisonable MonadPoisonable))
         A B
         ma k = raise_poison dt ->
      ma = raise_poison dt \/ exists a, ma = ret a /\ k a = raise_poison dt.
  Proof.
    intros A B ma k res H.
    destruct ma, unEitherT, unMkOomableT; inv H.
    repeat break_match_hyp_inv.
    - right.
      exists a.
      split; auto.
      cbn.
      destruct (k a), unEitherT, unMkOomableT; inv H1.
      reflexivity.
    - left.
      cbn.
      reflexivity.
  Qed.

  Lemma ErrOOMPoison_bind_raise_oom_inv :
    forall {A B} ma k dt,
      @bind ErrOOMPoison
        (@EitherMonad.Monad_eitherT ERR_MESSAGE (OomableT Poisonable)
           (@Monad_OomableT Poisonable MonadPoisonable))
        A B
        ma k = raise_oomable dt ->
      ma = raise_oomable dt \/ exists a, ma = ret a /\ k a = raise_oomable dt.
  Proof.
    intros A B ma k res H.
    destruct ma, unEitherT, unMkOomableT; inv H.
    repeat break_match_hyp_inv.
    - right.
      exists a.
      split; auto.
      cbn.
      destruct (k a), unEitherT, unMkOomableT; inv H1.
      reflexivity.
    - left.
      cbn.
      reflexivity.
  Qed.

  Lemma list_dvalue_bytes_to_dvalue_fin_inf :
    forall (dts : list dtyp) (pad : option N) (offset : N) (dvbs_fin : list dvalue_byte) (dvbs_inf : list IS1.MEM.DVALUE_BYTE.dvalue_byte) (res : ErrOOMPoison (list dvalue))
      (IH : forall u : dtyp,
          In u dts ->
          forall (dvbs_fin : list dvalue_byte) (dvbs_inf : list IS1.MEM.DVALUE_BYTE.dvalue_byte)
            (res : ErrOOMPoison dvalue),
            dvalue_bytes_refine dvbs_inf dvbs_fin ->
            (forall x : dtyp, res <> raise_oomable x) ->
            dvalue_bytes_to_dvalue dvbs_fin u = res ->
            IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue dvbs_inf u = fmap fin_to_inf_dvalue res),
      dvalue_bytes_refine dvbs_inf dvbs_fin ->
      (forall x : dtyp, res <> raise_oomable x) ->
      (fix go (offset : N) (dts : list dtyp) (dbs : list dvalue_byte) {struct dts} :
         ErrOOMPoison (list dvalue) :=
         match dts with
         | [] =>
             (* TODO: should we check that we have the appropriate number of extra padding bytes here? *)
             (* Long term we'll have to include padding bytes in the dvalue *)
             ret []
         | (dt::dts) =>
             let padding :=
               if pad
               then pad_amount (preferred_alignment (SIZEOF.dtyp_alignment dt)) offset
               else 0%N
             in
             let zpadding := Z.of_N padding in
             let sz := SIZEOF.sizeof_dtyp dt in
             (* Skip any padding bytes *)
             let dbs' := drop padding dbs in
             let init_bytes := take sz dbs' in
             let rest_bytes := drop sz dbs' in
             let offset' := (offset + padding)%N in
             f <- dvalue_bytes_to_dvalue init_bytes dt;;
             rest <- go (offset' + sz) dts rest_bytes;;
             ret (f :: rest)
         end) offset dts dvbs_fin = res ->
      (fix go (offset : N) (dts : list dtyp) (dbs : list IS1.MEM.DVALUE_BYTE.dvalue_byte) {struct dts} :=
         match dts with
         | [] =>
             (* TODO: should we check that we have the appropriate number of extra padding bytes here? *)
             (* Long term we'll have to include padding bytes in the dvalue *)
             ret []
         | (dt::dts) =>
             let padding :=
               if pad
               then pad_amount (preferred_alignment (IS1.LP.SIZEOF.dtyp_alignment dt)) offset
               else 0%N
             in
             let zpadding := Z.of_N padding in
             let sz := IS1.LP.SIZEOF.sizeof_dtyp dt in
             (* Skip any padding bytes *)
             let dbs' := drop padding dbs in
             let init_bytes := take sz dbs' in
             let rest_bytes := drop sz dbs' in
             let offset' := offset + padding in
             f <- IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue init_bytes dt;;
             rest <- go (offset' + sz) dts rest_bytes;;
             ret (f :: rest)
         end) offset dts dvbs_inf = fmap (map fin_to_inf_dvalue) res.
  Proof.
    induction dts; intros pad offset dvbs_fin dvbs_inf res IH REF NOOM FIN.
    - inv FIN; reflexivity.
    - Opaque bind.
      cbn in *.
      rewrite sizeof_dtyp_fin_inf.
      rewrite dtyp_alignment_fin_inf.
      erewrite IH; eauto.
      2: {
        apply Forall2_take; eauto.
        apply Forall2_drop; eauto.
      }
      2: {
        intros x CONTRA.
        eapply (NOOM x).
        subst.
        setoid_rewrite CONTRA.
        Transparent bind.
        cbn.
        reflexivity.
      }

      remember (dvalue_bytes_to_dvalue
                  (take (SIZEOF.sizeof_dtyp a)
                     (drop (if pad then pad_amount (preferred_alignment (SIZEOF.dtyp_alignment a)) offset else 0)
                        dvbs_fin)) a) as init.
      destruct_err_oom_poison init;
        try solve [subst; cbn; eauto].

      remember
        ((fix go (offset : N) (dts : list dtyp) (dbs : list dvalue_byte) {struct dts} :
           ErrOOMPoison (list dvalue) :=
            match dts with
            | [] => {| EitherMonad.unEitherT := {| unMkOomableT := Unpoisoned (Unoomed (inr [])) |} |}
            | dt :: dts0 =>
                f0 <-
                  dvalue_bytes_to_dvalue
                    (take (SIZEOF.sizeof_dtyp dt)
                       (drop
                          (if pad
                           then pad_amount (preferred_alignment (SIZEOF.dtyp_alignment dt)) offset
                           else 0) dbs)) dt;;
                rest <-
                  go
                    (offset +
                       (if pad then pad_amount (preferred_alignment (SIZEOF.dtyp_alignment dt)) offset else 0) +
                       SIZEOF.sizeof_dtyp dt) dts0
                    (drop (SIZEOF.sizeof_dtyp dt)
                       (drop
                          (if pad
                           then pad_amount (preferred_alignment (SIZEOF.dtyp_alignment dt)) offset
                           else 0) dbs));;
                {|
                  EitherMonad.unEitherT := {| unMkOomableT := Unpoisoned (Unoomed (inr (f0 :: rest))) |}
                |}
            end)
           (offset + (if pad then pad_amount (preferred_alignment (SIZEOF.dtyp_alignment a)) offset else 0) +
              SIZEOF.sizeof_dtyp a) dts
           (drop (SIZEOF.sizeof_dtyp a)
              (drop (if pad then pad_amount (preferred_alignment (SIZEOF.dtyp_alignment a)) offset else 0)
                 dvbs_fin))) as rest.

      erewrite IHdts with (res:=rest).
      + destruct_err_oom_poison rest;
          try solve [subst; cbn; eauto].
      + eauto.
      + eapply Forall2_drop; eauto.
        eapply Forall2_drop; eauto.
      + intros x CONTRA; subst.
        specialize (NOOM x).
        eapply NOOM.
        rewrite CONTRA.
        Transparent bind.
        cbn.
        reflexivity.
      + subst.
        reflexivity.
  Qed.

  Lemma dvalue_bytes_fin_to_dvalue_fin_inf :
    forall dt dvbs_fin dvbs_inf res,
      dvalue_bytes_refine dvbs_inf dvbs_fin ->
      (forall x, res <> raise_oomable x) ->
      (@dvalue_bytes_to_dvalue ErrOOMPoison
         (@EitherMonad.Monad_eitherT ERR_MESSAGE
            (OomableT Poisonable)
            (@Monad_OomableT Poisonable MonadPoisonable))
         (@RAISE_ERROR_MonadExc ErrOOMPoison
            (@EitherMonad.Exception_eitherT ERR_MESSAGE
               (OomableT Poisonable)
               (@Monad_OomableT Poisonable MonadPoisonable)))
         (@RAISE_POISON_E_MT (OomableT Poisonable)
            (EitherMonad.eitherT ERR_MESSAGE)
            (@EitherMonad.MonadT_eitherT ERR_MESSAGE
               (OomableT Poisonable)
               (@Monad_OomableT Poisonable MonadPoisonable))
            (@RAISE_POISON_E_MT Poisonable OomableT
               (@MonadT_OomableT Poisonable MonadPoisonable)
               RAISE_POISON_Poisonable))
         (@RAISE_OOMABLE_E_MT (OomableT Poisonable)
            (EitherMonad.eitherT ERR_MESSAGE)
            (@EitherMonad.MonadT_eitherT ERR_MESSAGE
               (OomableT Poisonable)
               (@Monad_OomableT Poisonable MonadPoisonable))
            (@RAISE_OOMABLE_OomableT Poisonable MonadPoisonable)) dvbs_fin dt) = res ->
      (@IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue ErrOOMPoison
         (@EitherMonad.Monad_eitherT ERR_MESSAGE
            (OomableT Poisonable)
            (@Monad_OomableT Poisonable
               MonadPoisonable))
         (@RAISE_ERROR_MonadExc ErrOOMPoison
            (@EitherMonad.Exception_eitherT ERR_MESSAGE
               (OomableT Poisonable)
               (@Monad_OomableT Poisonable
                  MonadPoisonable)))
         (@RAISE_POISON_E_MT
            (OomableT Poisonable)
            (EitherMonad.eitherT ERR_MESSAGE)
            (@EitherMonad.MonadT_eitherT ERR_MESSAGE
               (OomableT Poisonable)
               (@Monad_OomableT Poisonable
                  MonadPoisonable))
            (@RAISE_POISON_E_MT Poisonable
               OomableT
               (@MonadT_OomableT Poisonable
                  MonadPoisonable)
               RAISE_POISON_Poisonable))
         (@RAISE_OOMABLE_E_MT
            (OomableT Poisonable)
            (EitherMonad.eitherT ERR_MESSAGE)
            (@EitherMonad.MonadT_eitherT ERR_MESSAGE
               (OomableT Poisonable)
               (@Monad_OomableT Poisonable
                  MonadPoisonable))
            (@RAISE_OOMABLE_OomableT Poisonable
               MonadPoisonable)) dvbs_inf dt) = fmap fin_to_inf_dvalue res.
  Proof.
    induction dt;
      intros dvbs_fin dvbs_inf res REF NOOM FIN;
      try
        solve
        [ rewrite dvalue_bytes_to_dvalue_equation in FIN;
          rewrite IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue_equation;
          subst;
          erewrite map_monad_dvalue_byte_value_fin_inf; eauto;
          remember (map_monad IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte_value dvbs_inf) as res;
          destruct_err_oom_poison res; cbn; auto;
          cbn;
          repeat break_match_goal;
          try inv Heqp0;
          try inv Heqp1;
          try inv Heqp2;
          try inv Heqp3;
          try inv Heqp4;
          try inv Heqp5;
          try inv Heqp6;
          try inv Heqp7;
          try inv Heqp;
          try reflexivity;
          rewrite_fin_to_inf_dvalue; auto
        | rewrite dvalue_bytes_to_dvalue_equation in FIN;
          rewrite IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue_equation;
          subst;
          reflexivity
        ].

    { rewrite dvalue_bytes_to_dvalue_equation in FIN;
        rewrite IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue_equation;
        subst.
      erewrite map_monad_dvalue_byte_value_fin_inf in NOOM; eauto.
      erewrite map_monad_dvalue_byte_value_fin_inf; eauto;
        remember (map_monad IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte_value dvbs_inf) as res.
      destruct_err_oom_poison res; cbn; auto.
      remember (lift_OOMABLE DTYPE_IPTR (IP.from_Z (concat_bytes_Z res0))) as y.
      destruct_err_oom_poison y; cbn; auto;
        unfold lift_OOMABLE in Heqy; break_match_hyp_inv.
      2: {
        cbn in *.
        specialize (NOOM DTYPE_IPTR).
        rewrite Heqo in NOOM.
        contradiction.
      }

      pose proof intptr_convert_succeeds i as (?&?).
      eapply intptr_convert_safe in e.
      pose proof IP.from_Z_injective _ _ _ Heqo e.
      rewrite H.
      rewrite IS1.LP.IP.to_Z_from_Z; cbn.
      rewrite_fin_to_inf_dvalue.
      unfold intptr_fin_inf.
      break_match_goal.
      clear Heqs.
      eapply intptr_convert_safe in e0.
      pose proof IP.from_Z_injective _ _ _ e e0.
      apply IS1.LP.IP.to_Z_inj in H0; subst; auto.
    }

    { rewrite dvalue_bytes_to_dvalue_equation in FIN;
        rewrite IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue_equation;
        subst.
      erewrite map_monad_dvalue_byte_value_fin_inf in NOOM; eauto.
      erewrite map_monad_dvalue_byte_value_fin_inf; eauto;
        remember (map_monad IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte_value dvbs_inf) as res.
      destruct_err_oom_poison res; cbn; auto.
      specialize (NOOM DTYPE_Pointer).
      cbn in NOOM.
      break_match_hyp; try contradiction.
      clear NOOM.
      erewrite int_to_ptr_fin_inf_wildcard; eauto.
      cbn.
      rewrite_fin_to_inf_dvalue.
      reflexivity.

      unfold fin_to_inf_addr.
      break_match_goal; clear Heqs; auto.
    }

    { (* Arrays *)
      rewrite dvalue_bytes_to_dvalue_equation in FIN;
        rewrite IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue_equation;
        subst.
      rewrite sizeof_dtyp_fin_inf.
      Opaque IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue
        dvalue_bytes_to_dvalue.
      cbn in *.
      destruct ((SIZEOF.sizeof_dtyp dt =? 0)%N) eqn:HSIZE.
      { clear - IHdt NOOM.
        induction sz using N.peano_ind.
        - cbn.
          rewrite_fin_to_inf_dvalue.
          reflexivity.
        - setoid_rewrite repeatN_succ.
          cbn.
          repeat rewrite_fin_to_inf_dvalue.
          remember (dvalue_bytes_to_dvalue [] dt) as res.
          symmetry in Heqres.
          pose proof (IHdt nil nil res).
          forward H; [constructor|].
          destruct_err_oom_poison res; cbn in *;
            try solve [setoid_rewrite H; cbn; eauto; try discriminate].
          + (* Success *)
            setoid_rewrite H; cbn; eauto; try discriminate.
            forward IHsz.
            { intros x CONTRA.
              eapply NOOM.
              rewrite repeatN_succ.
              cbn.
              rewrite Heqres.
              cbn.
              remember (map_monad (fun es : list dvalue_byte => dvalue_bytes_to_dvalue es dt)
                          (repeatN sz [])) as m.
              destruct_err_oom_poison m; cbn in *; try discriminate; eauto.
            }

            remember (map_monad
                      (fun es : list IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte =>
                       IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue es dt) 
                      (repeatN sz [])) as m1.
            remember (map_monad (fun es : list dvalue_byte => dvalue_bytes_to_dvalue es dt)
               (repeatN sz [])) as m2.
            destruct_err_oom_poison m1;
              destruct_err_oom_poison m2; cbn in *; try discriminate; eauto.
            rewrite_fin_to_inf_dvalue.
            cbn.
            inv IHsz.
            rewrite fin_to_inf_dvalue_array in H1.
            inv H1.
            auto.
          + (* OOM *)
            exfalso.
            clear H IHdt.
            eapply NOOM.
            rewrite repeatN_succ.
            cbn.
            rewrite Heqres.
            cbn.
            reflexivity.
      }

      remember (split_every_nil (SIZEOF.sizeof_dtyp dt) dvbs_fin) as split_fin.
      remember (split_every_nil (SIZEOF.sizeof_dtyp dt) dvbs_inf) as split_inf.
      symmetry in Heqsplit_fin, Heqsplit_inf.

      pose proof split_every_nil_Forall2 _ _ _ _ _ _ REF Heqsplit_inf Heqsplit_fin as ALL.
      subst.
      induction ALL.
      - cbn.
        rewrite_fin_to_inf_dvalue; reflexivity.
      - repeat rewrite map_monad_unfold.
        cbn.
        erewrite IHdt.
        2: apply H.
        3: eauto.
        2: {
          clear - NOOM.
          rewrite map_monad_unfold in *.
          cbn in *.
          remember (dvalue_bytes_to_dvalue y dt) as r.
          intros x CONTRA.
          destruct_err_oom_poison r; inv CONTRA.
          cbn in NOOM.
          specialize (NOOM x); contradiction.
        }

        remember (dvalue_bytes_to_dvalue y dt) as r.
        destruct_err_oom_poison r; cbn; auto.
        remember (map_monad (fun x0 : list dvalue_byte => dvalue_bytes_to_dvalue x0 dt) l') as m.
        forward IHALL.
        { intros x0.
          destruct_err_oom_poison m; cbn; intros CONTRA; inv CONTRA.
          cbn in NOOM.
          repeat rewrite <- Heqr, <- Heqm in NOOM.
          cbn in NOOM.
          specialize (NOOM x0).
          contradiction.
        }

        destruct_err_oom_poison m; cbn; auto.
        + cbn in IHALL.
          remember (map_monad
                            (fun es : list IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte =>
                               IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue es dt) l) as w.
          destruct_err_oom_poison w; cbn in *; auto; inv IHALL.
        + cbn in IHALL.
          remember (map_monad
                            (fun es : list IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte =>
                               IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue es dt) l) as w.
          destruct_err_oom_poison w; cbn in *; auto; inv IHALL.
          rewrite_fin_to_inf_dvalue; auto.
          cbn.
          rewrite fin_to_inf_dvalue_array in H1.
          inv H1.
          reflexivity.
        + cbn in IHALL.
          remember (map_monad
                            (fun es : list IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte =>
                               IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue es dt) l) as w.
          destruct_err_oom_poison w; cbn in *; auto; inv IHALL.
        + cbn in IHALL.
          remember (map_monad
                            (fun es : list IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte =>
                               IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue es dt) l) as w.
          destruct_err_oom_poison w; cbn in *; auto; inv IHALL.
    }

    { (* Structs *)
      Opaque IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue
        dvalue_bytes_to_dvalue.

      subst.
      rewrite IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue_equation,
        dvalue_bytes_to_dvalue_equation.

      remember
        (fun pad : option N => fix go
           (offset : N) (dts : list dtyp) (dbs : list IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte) {struct dts} :
          ErrOOMPoison (list IS1.LP.Events.DV.dvalue) :=
           match dts with
           | [] => ret []
           | dt :: dts0 =>
               let padding :=
                 if pad
                 then pad_amount (preferred_alignment (IS1.LP.SIZEOF.dtyp_alignment dt)) offset
                 else 0 in
               let zpadding := Z.of_N padding in
               let sz := IS1.LP.SIZEOF.sizeof_dtyp dt in
               let dbs' := drop padding dbs in
               let init_bytes := take sz dbs' in
               let rest_bytes := drop sz dbs' in
               let offset' := offset + padding in
               f <- IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue init_bytes dt;;
               rest <- go (offset' + sz) dts0 rest_bytes;; ret (f :: rest)
           end) as f1.

      remember
        (fun pad : option N =>
           fix go (offset : N) (dts : list dtyp) (dbs : list dvalue_byte) {struct dts} :
           ErrOOMPoison (list dvalue) :=
           match dts with
           | [] => ret []
           | dt :: dts0 =>
               let padding :=
                 if pad then pad_amount (preferred_alignment (SIZEOF.dtyp_alignment dt)) offset else 0
               in
               let zpadding := Z.of_N padding in
               let sz := SIZEOF.sizeof_dtyp dt in
               let dbs' := drop padding dbs in
               let init_bytes := take sz dbs' in
               let rest_bytes := drop sz dbs' in
               let offset' := offset + padding in
               f <- dvalue_bytes_to_dvalue init_bytes dt;;
               rest <- go (offset' + sz) dts0 rest_bytes;; ret (f :: rest)
           end) as f2.
      Opaque bind.
      cbn.
      subst.
      erewrite list_dvalue_bytes_to_dvalue_fin_inf with (pad:=Some 1); eauto.
      { Transparent bind.
        remember
          (((fix go (offset : N) (dts : list dtyp) (dbs : list dvalue_byte) {struct dts} :
             ErrOOMPoison (list dvalue) :=
           match dts with
           | [] => ret []
           | dt :: dts0 =>
               let padding := pad_amount (preferred_alignment (SIZEOF.dtyp_alignment dt)) offset in
               let zpadding := Z.of_N padding in
               let sz := SIZEOF.sizeof_dtyp dt in
               let dbs' := drop padding dbs in
               let init_bytes := take sz dbs' in
               let rest_bytes := drop sz dbs' in
               let offset' := offset + padding in
               f <- dvalue_bytes_to_dvalue init_bytes dt;;
               rest <- go (offset' + sz) dts0 rest_bytes;; ret (f :: rest)
           end) 0 fields dvbs_fin)) as res.
        destruct_err_oom_poison res; cbn; auto.
        rewrite_fin_to_inf_dvalue.
        reflexivity.
      }

      intros x CONTRA.
      eapply (NOOM x).
      cbn.
      rewrite dvalue_bytes_to_dvalue_equation.
      remember
        ((fun pad : option N =>
           fix go (offset : N) (dts : list dtyp) (dbs : list dvalue_byte) {struct dts} :
           ErrOOMPoison (list dvalue) :=
           match dts with
           | [] => ret []
           | dt :: dts0 =>
               let padding :=
                 if pad then pad_amount (preferred_alignment (SIZEOF.dtyp_alignment dt)) offset else 0 in
               let zpadding := Z.of_N padding in
               let sz := SIZEOF.sizeof_dtyp dt in
               let dbs' := drop padding dbs in
               let init_bytes := take sz dbs' in
               let rest_bytes := drop sz dbs' in
               let offset' := offset + padding in
               f <- dvalue_bytes_to_dvalue init_bytes dt;;
               rest <- go (offset' + sz) dts0 rest_bytes;; ret (f :: rest)
           end) (Some (SIZEOF.max_preferred_dtyp_alignment fields)) 0 fields dvbs_fin) as res.
      destruct_err_oom_poison res; inv CONTRA; cbn in *; auto;
      setoid_rewrite H1;
      cbn;
      auto.
    }

    { (* Packed structs *)
      Opaque IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue
        dvalue_bytes_to_dvalue.

      subst.
      rewrite IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue_equation,
        dvalue_bytes_to_dvalue_equation.

      remember
        (fun pad : option N => fix go
           (offset : N) (dts : list dtyp) (dbs : list IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte) {struct dts} :
          ErrOOMPoison (list IS1.LP.Events.DV.dvalue) :=
           match dts with
           | [] => ret []
           | dt :: dts0 =>
               let padding :=
                 if pad
                 then pad_amount (preferred_alignment (IS1.LP.SIZEOF.dtyp_alignment dt)) offset
                 else 0 in
               let zpadding := Z.of_N padding in
               let sz := IS1.LP.SIZEOF.sizeof_dtyp dt in
               let dbs' := drop padding dbs in
               let init_bytes := take sz dbs' in
               let rest_bytes := drop sz dbs' in
               let offset' := offset + padding in
               f <- IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue init_bytes dt;;
               rest <- go (offset' + sz) dts0 rest_bytes;; ret (f :: rest)
           end) as f1.

      remember
        (fun pad : option N =>
           fix go (offset : N) (dts : list dtyp) (dbs : list dvalue_byte) {struct dts} :
           ErrOOMPoison (list dvalue) :=
           match dts with
           | [] => ret []
           | dt :: dts0 =>
               let padding :=
                 if pad then pad_amount (preferred_alignment (SIZEOF.dtyp_alignment dt)) offset else 0
               in
               let zpadding := Z.of_N padding in
               let sz := SIZEOF.sizeof_dtyp dt in
               let dbs' := drop padding dbs in
               let init_bytes := take sz dbs' in
               let rest_bytes := drop sz dbs' in
               let offset' := offset + padding in
               f <- dvalue_bytes_to_dvalue init_bytes dt;;
               rest <- go (offset' + sz) dts0 rest_bytes;; ret (f :: rest)
           end) as f2.
      Opaque bind.
      cbn.
      subst.
      erewrite list_dvalue_bytes_to_dvalue_fin_inf with (pad:=None); eauto.
      { Transparent bind.
        remember
          (((fix go (offset : N) (dts : list dtyp) (dbs : list dvalue_byte) {struct dts} :
             ErrOOMPoison (list dvalue) :=
           match dts with
           | [] => ret []
           | dt :: dts0 =>
               let padding := 0 in
               let zpadding := Z.of_N padding in
               let sz := SIZEOF.sizeof_dtyp dt in
               let dbs' := drop padding dbs in
               let init_bytes := take sz dbs' in
               let rest_bytes := drop sz dbs' in
               let offset' := offset + padding in
               f <- dvalue_bytes_to_dvalue init_bytes dt;;
               rest <- go (offset' + sz) dts0 rest_bytes;; ret (f :: rest)
           end) 0 fields dvbs_fin)) as res.
        destruct_err_oom_poison res; cbn; auto.
        rewrite_fin_to_inf_dvalue.
        reflexivity.
      }

      intros x CONTRA.
      eapply (NOOM x).
      cbn.
      rewrite dvalue_bytes_to_dvalue_equation.
      remember
        ((fun pad : option N =>
           fix go (offset : N) (dts : list dtyp) (dbs : list dvalue_byte) {struct dts} :
           ErrOOMPoison (list dvalue) :=
           match dts with
           | [] => ret []
           | dt :: dts0 =>
               let padding :=
                 if pad then pad_amount (preferred_alignment (SIZEOF.dtyp_alignment dt)) offset else 0 in
               let zpadding := Z.of_N padding in
               let sz := SIZEOF.sizeof_dtyp dt in
               let dbs' := drop padding dbs in
               let init_bytes := take sz dbs' in
               let rest_bytes := drop sz dbs' in
               let offset' := offset + padding in
               f <- dvalue_bytes_to_dvalue init_bytes dt;;
               rest <- go (offset' + sz) dts0 rest_bytes;; ret (f :: rest)
           end) None 0 fields dvbs_fin) as res.
      destruct_err_oom_poison res; inv CONTRA; cbn in *; auto;
      setoid_rewrite H1;
      cbn;
      auto.
    }

    { (* Vectors *)
      rewrite dvalue_bytes_to_dvalue_equation in FIN;
        rewrite IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue_equation;
        subst.
      rewrite sizeof_dtyp_fin_inf.
      Opaque IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue
        dvalue_bytes_to_dvalue.
      cbn in *.
      destruct ((SIZEOF.sizeof_dtyp dt =? 0)%N) eqn:HSIZE.
      { clear - IHdt NOOM.
        induction sz using N.peano_ind.
        - cbn.
          rewrite_fin_to_inf_dvalue.
          reflexivity.
        - setoid_rewrite repeatN_succ.
          cbn.
          repeat rewrite_fin_to_inf_dvalue.
          remember (dvalue_bytes_to_dvalue [] dt) as res.
          symmetry in Heqres.
          pose proof (IHdt nil nil res).
          forward H; [constructor|].
          destruct_err_oom_poison res; cbn in *;
            try solve [setoid_rewrite H; cbn; eauto; try discriminate].
          + (* Success *)
            setoid_rewrite H; cbn; eauto; try discriminate.
            forward IHsz.
            { intros x CONTRA.
              eapply NOOM.
              rewrite repeatN_succ.
              cbn.
              rewrite Heqres.
              cbn.
              remember (map_monad (fun es : list dvalue_byte => dvalue_bytes_to_dvalue es dt)
                          (repeatN sz [])) as m.
              destruct_err_oom_poison m; cbn in *; try discriminate; eauto.
            }

            remember (map_monad
                      (fun es : list IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte =>
                       IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue es dt) 
                      (repeatN sz [])) as m1.
            remember (map_monad (fun es : list dvalue_byte => dvalue_bytes_to_dvalue es dt)
               (repeatN sz [])) as m2.
            destruct_err_oom_poison m1;
              destruct_err_oom_poison m2; cbn in *; try discriminate; eauto.
            rewrite_fin_to_inf_dvalue.
            cbn.
            inv IHsz.
            rewrite fin_to_inf_dvalue_vector in H1.
            inv H1.
            auto.
          + (* OOM *)
            exfalso.
            clear H IHdt.
            eapply NOOM.
            rewrite repeatN_succ.
            cbn.
            rewrite Heqres.
            cbn.
            reflexivity.
      }

      remember (split_every_nil (SIZEOF.sizeof_dtyp dt) dvbs_fin) as split_fin.
      remember (split_every_nil (SIZEOF.sizeof_dtyp dt) dvbs_inf) as split_inf.
      symmetry in Heqsplit_fin, Heqsplit_inf.

      pose proof split_every_nil_Forall2 _ _ _ _ _ _ REF Heqsplit_inf Heqsplit_fin as ALL.
      subst.
      induction ALL.
      - cbn.
        rewrite_fin_to_inf_dvalue; reflexivity.
      - repeat rewrite map_monad_unfold.
        cbn.
        erewrite IHdt.
        2: apply H.
        3: eauto.
        2: {
          clear - NOOM.
          rewrite map_monad_unfold in *.
          cbn in *.
          remember (dvalue_bytes_to_dvalue y dt) as r.
          intros x CONTRA.
          destruct_err_oom_poison r; inv CONTRA.
          cbn in NOOM.
          specialize (NOOM x); contradiction.
        }

        remember (dvalue_bytes_to_dvalue y dt) as r.
        destruct_err_oom_poison r; cbn; auto.
        remember (map_monad (fun x0 : list dvalue_byte => dvalue_bytes_to_dvalue x0 dt) l') as m.
        forward IHALL.
        { intros x0.
          destruct_err_oom_poison m; cbn; intros CONTRA; inv CONTRA.
          cbn in NOOM.
          repeat rewrite <- Heqr, <- Heqm in NOOM.
          cbn in NOOM.
          specialize (NOOM x0).
          contradiction.
        }

        destruct_err_oom_poison m; cbn; auto.
        + cbn in IHALL.
          remember (map_monad
                            (fun es : list IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte =>
                               IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue es dt) l) as w.
          destruct_err_oom_poison w; cbn in *; auto; inv IHALL.
        + cbn in IHALL.
          remember (map_monad
                            (fun es : list IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte =>
                               IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue es dt) l) as w.
          destruct_err_oom_poison w; cbn in *; auto; inv IHALL.
          rewrite_fin_to_inf_dvalue; auto.
          cbn.
          rewrite fin_to_inf_dvalue_vector in H1.
          inv H1.
          reflexivity.
        + cbn in IHALL.
          remember (map_monad
                            (fun es : list IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte =>
                               IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue es dt) l) as w.
          destruct_err_oom_poison w; cbn in *; auto; inv IHALL.
        + cbn in IHALL.
          remember (map_monad
                            (fun es : list IS1.LLVM.MEM.DVALUE_BYTE.dvalue_byte =>
                               IS1.LLVM.MEM.DVALUE_BYTE.dvalue_bytes_to_dvalue es dt) l) as w.
          destruct_err_oom_poison w; cbn in *; auto; inv IHALL.
    }
  Qed.

  Lemma dvalue_bytes_to_dvalue_fin_inf :
    forall τ dvbs_inf dvbs_fin res,
      dvalue_bytes_refine dvbs_inf dvbs_fin ->
      @ErrOOMPoison_handle_poison_and_oom (err_ub_oom_T IdentityMonad.ident)
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident) dvalue
        DVALUE_Poison (DVALUE_BYTES.dvalue_bytes_to_dvalue dvbs_fin τ) = success_unERR_UB_OOM res ->
      @ErrOOMPoison_handle_poison_and_oom (err_ub_oom_T IdentityMonad.ident)
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        IS1.LP.Events.DV.dvalue IS1.LP.Events.DV.DVALUE_Poison (IS1.LLVM.MEM.MP.DVALUE_BYTES.dvalue_bytes_to_dvalue dvbs_inf τ) = success_unERR_UB_OOM (fin_to_inf_dvalue res).
  Proof.
    intros τ dvbs_inf dvbs_fin res H H0.
    remember (@DVALUE_BYTES.dvalue_bytes_to_dvalue ErrOOMPoison
            (@EitherMonad.Monad_eitherT ERR_MESSAGE (OomableT Poisonable)
               (@Monad_OomableT Poisonable MonadPoisonable))
            (@RAISE_ERROR_MonadExc ErrOOMPoison
               (@EitherMonad.Exception_eitherT ERR_MESSAGE (OomableT Poisonable)
                  (@Monad_OomableT Poisonable MonadPoisonable)))
            (@RAISE_POISON_E_MT (OomableT Poisonable) (EitherMonad.eitherT ERR_MESSAGE)
               (@EitherMonad.MonadT_eitherT ERR_MESSAGE (OomableT Poisonable)
                  (@Monad_OomableT Poisonable MonadPoisonable))
               (@RAISE_POISON_E_MT Poisonable OomableT (@MonadT_OomableT Poisonable MonadPoisonable)
                  RAISE_POISON_Poisonable))
            (@RAISE_OOMABLE_E_MT (OomableT Poisonable) (EitherMonad.eitherT ERR_MESSAGE)
               (@EitherMonad.MonadT_eitherT ERR_MESSAGE (OomableT Poisonable)
                  (@Monad_OomableT Poisonable MonadPoisonable))
               (@RAISE_OOMABLE_OomableT Poisonable MonadPoisonable)) dvbs_fin τ).
    destruct e.
    destruct unEitherT.
    destruct unMkOomableT; inv H0.
    2: {
      unfold ErrOOMPoison_handle_poison_and_oom.
      symmetry in Heqe.
      erewrite dvalue_bytes_fin_to_dvalue_fin_inf; eauto.
      cbn; rewrite_fin_to_inf_dvalue; eauto.
      intros ? CONTRA; inv CONTRA.
    }
    destruct o; inv H2.
    repeat red in H1.
    unfold ErrOOMPoison_handle_poison_and_oom in H1.
    cbn in H1.
    destruct s; inv H1.
    destruct e; inv H2.
    unfold ErrOOMPoison_handle_poison_and_oom.
    erewrite dvalue_bytes_fin_to_dvalue_fin_inf; eauto.
    2: {
      intros ? CONTRA.
      rewrite <- Heqe in CONTRA.
      inv CONTRA.
    }
    rewrite <- Heqe.
    cbn; reflexivity.
  Qed.

  Lemma dvalue_to_dvalue_bytes_fin_to_inf_dvalue :
    forall dv_fin t,
      IS1.LLVM.MEM.MP.DVALUE_BYTES.dvalue_to_dvalue_bytes (fin_to_inf_dvalue dv_fin) t =
        fin_to_inf_dvalue_bytes (dvalue_to_dvalue_bytes dv_fin t).
  Proof.
    intros dv_fin t.
    destruct dv_fin;
      rewrite_fin_to_inf_dvalue;
      try
        solve
        [ erewrite <- dvalue_to_dvalue_bytes_fin_inf; eauto;
          reflexivity
        ].

    - erewrite <- dvalue_to_dvalue_bytes_fin_inf; eauto.
      red.
      cbn.
      rewrite addr_refine_fin_to_inf_addr.
      reflexivity.
    - erewrite <- dvalue_to_dvalue_bytes_fin_inf; eauto.
      red.
      cbn.
      pose proof intptr_convert_succeeds x as (?&?).
      eapply intptr_convert_safe in e.
      erewrite intptr_convert_safe.
      reflexivity.
      unfold intptr_fin_inf.
      break_match_goal.
      clear Heqs.
      auto.
    - erewrite <- dvalue_to_dvalue_bytes_fin_inf; eauto.
      red.
      cbn.
      induction fields.
      + cbn; reflexivity.
      + cbn.
        break_match_hyp_inv.
        rewrite fin_to_inf_dvalue_refine_strict.
        reflexivity.
    - erewrite <- dvalue_to_dvalue_bytes_fin_inf; eauto.
      red.
      cbn.
      induction fields.
      + cbn; reflexivity.
      + cbn.
        break_match_hyp_inv.
        rewrite fin_to_inf_dvalue_refine_strict.
        reflexivity.
    - erewrite <- dvalue_to_dvalue_bytes_fin_inf; eauto.
      red.
      cbn.
      induction elts.
      + cbn; reflexivity.
      + cbn.
        break_match_hyp_inv.
        rewrite fin_to_inf_dvalue_refine_strict.
        reflexivity.
    - erewrite <- dvalue_to_dvalue_bytes_fin_inf; eauto.
      red.
      cbn.
      induction elts.
      + cbn; reflexivity.
      + cbn.
        break_match_hyp_inv.
        rewrite fin_to_inf_dvalue_refine_strict.
        reflexivity.
  Qed.

  Lemma get_conv_case_pure_fin_inf:
    forall conv t_from dv t_to res,
      get_conv_case conv t_from dv t_to = Conv_Pure res ->
      IS1.LLVM.MEM.CP.CONC.get_conv_case conv t_from (fin_to_inf_dvalue dv) t_to = IS1.LP.Events.DV.Conv_Pure (fin_to_inf_dvalue res).
  Proof.
    intros conv t_from dv t_to res CONV.
    destruct conv.
    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        unfold fin_to_inf_uvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;
        try (inv H0; subst_existT; try rewrite Heqb; auto; break_match_goal; clear Heqs; destruct p; clear e0;
             cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        unfold fin_to_inf_uvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;
        try (inv H0; subst_existT; try rewrite Heqb; auto; break_match_goal; clear Heqs; destruct p; clear e0;
             cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        unfold fin_to_inf_uvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;
        try (inv H0; subst_existT; try rewrite Heqb; auto; break_match_goal; clear Heqs; destruct p; clear e0;
             cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue, fin_to_inf_uvalue; inv CONV.
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue, fin_to_inf_uvalue; inv CONV.
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        unfold fin_to_inf_uvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;
        try (inv H0; subst_existT; try rewrite Heqb; auto; break_match_goal; clear Heqs; destruct p; clear e0;
             cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        unfold fin_to_inf_uvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;
        try (inv H0; subst_existT; try rewrite Heqb; auto; break_match_goal; clear Heqs; destruct p; clear e0;
             cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        unfold fin_to_inf_uvalue;
        inv CONV.
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        unfold fin_to_inf_uvalue;
        inv CONV.
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        unfold fin_to_inf_uvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;

        try (inv H0; auto; break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        unfold fin_to_inf_uvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;

        try (inv H0; auto; break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; reflexivity).
    }

    { (* Conversions... *)
      unfold get_conv_case in CONV.
      unfold IS1.LLVM.MEM.CP.CONC.get_conv_case.

      repeat rewrite bit_sizeof_dtyp_fin_inf.
      unfold MemHelpers.dtyp_eqb,
        IS1.LLVM.MEM.CP.CONC.MemHelpers.dtyp_eqb in *.

      break_match_hyp.
      2: {
        break_match_hyp.
        - remember (ErrOOMPoison_handle_poison_and_oom DVALUE_Poison
                            (DVALUE_BYTES.dvalue_bytes_to_dvalue
                               (DVALUE_BYTES.dvalue_to_dvalue_bytes dv t_from) t_to)) as x.
          destruct_err_ub_oom x; inv CONV.
          erewrite dvalue_bytes_to_dvalue_fin_inf; eauto.
          cbn; auto.
          rewrite dvalue_to_dvalue_bytes_fin_to_inf_dvalue.
          apply dvalue_bytes_refine_fin_to_inf_dvalue_bytes.
        - inv CONV.
      }
      inv CONV; auto.
    }

    { (* Addrspacecast *)
      cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        break_match_goal; inv CONV.
    }
  Qed.

  Lemma get_conv_case_itop_fin_inf:
    forall conv t_from dv t_to res,
      get_conv_case conv t_from dv t_to = Conv_ItoP res ->
      IS1.LLVM.MEM.CP.CONC.get_conv_case conv t_from (fin_to_inf_dvalue dv) t_to = IS1.LP.Events.DV.Conv_ItoP (fin_to_inf_dvalue res).
  Proof.
    intros conv t_from dv t_to res CONV.
    destruct conv.
    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;

        try (inv H0; auto; break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;

        try (inv H0; auto; break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;

        try (inv H0; auto; break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue; inv CONV.
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue; inv CONV.
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;

        try (inv H0; auto; break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;

        try (inv H0; auto; break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        inv CONV.
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        inv CONV.
    }

    { (* inttoptr *)
      cbn in *.
      repeat break_match_hyp_inv; reflexivity.
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;

        try (inv H0; auto; break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; reflexivity).
    }

    { (* Conversions... *)
      unfold get_conv_case in CONV.
      unfold IS1.LLVM.MEM.CP.CONC.get_conv_case.

      repeat rewrite bit_sizeof_dtyp_fin_inf.
      repeat break_match_hyp_inv.
    }

    { (* Addrspacecast *)
      cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        break_match_goal; inv CONV.
    }
  Qed.

  Lemma get_conv_case_ptoi_fin_inf:
    forall conv t_from dv t_to res,
      get_conv_case conv t_from dv t_to = Conv_PtoI res ->
      IS1.LLVM.MEM.CP.CONC.get_conv_case conv t_from (fin_to_inf_dvalue dv) t_to = IS1.LP.Events.DV.Conv_PtoI (fin_to_inf_dvalue res).
  Proof.
    intros conv t_from dv t_to res CONV.
    destruct conv.
    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;

        try (inv H0; auto; break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;

        try (inv H0; auto; break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;

        try (inv H0; auto; break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue; inv CONV.
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue; inv CONV.
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;

        try (inv H0; auto; break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        break_match_goal; break_match_hyp; clear Heqs; destruct p; clear e0;
        cbn in e; inv e; try discriminate;

        try (inv H0; auto; break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; reflexivity).
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        inv CONV.
    }

    { cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        inv CONV.
    }

    { (* inttoptr *)
      cbn in *.
      repeat break_match_hyp_inv; reflexivity.
    }

    { cbn in *.
      repeat break_match_hyp_inv; auto.
    }

    { (* Conversions... *)
      unfold get_conv_case in CONV.
      unfold IS1.LLVM.MEM.CP.CONC.get_conv_case.

      repeat rewrite bit_sizeof_dtyp_fin_inf.
      repeat break_match_hyp_inv.
    }

    { (* Addrspacecast *)
      cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        break_match_goal; inv CONV.
    }
  Qed.

  Lemma handle_gep_h_fin_inf :
    forall  idxs_fin idxs_inf t base res,
      GEP.handle_gep_h t base idxs_fin = inr res ->
      map fin_to_inf_dvalue idxs_fin = idxs_inf ->
      IS1.LLVM.MEM.MP.GEP.handle_gep_h t base idxs_inf = inr res.
  Proof.
    induction idxs_fin;
      intros idxs_inf t base res GEP IDXS.
    - cbn in *; subst; cbn in *; auto.
    - cbn in *.
      (* Split based on index type *)
      break_match_hyp_inv; break_match_hyp_inv;
        try solve [ cbn;
                    rewrite H1;
                    rewrite_fin_to_inf_dvalue;
                    eapply IHidxs_fin in H1; eauto;
                    rewrite sizeof_dtyp_fin_inf;
                    rewrite H1;
                    auto
                  | cbn;
                    rewrite H1;
                    rewrite_fin_to_inf_dvalue;
                    rewrite sizeof_dtyp_fin_inf;
                    eapply IHidxs_fin in H1; eauto;
                    rewrite H1;
                    auto
          ].

      { (* ix *)
        cbn; rewrite_fin_to_inf_dvalue.
        repeat break_match_hyp_inv;
          try
            (try rewrite H0;
             try rewrite H1;
             try erewrite IHidxs_fin; eauto;
             try setoid_rewrite sizeof_dtyp_fin_inf;
             try setoid_rewrite padding_fin_inf;
             auto).

        - cbn.
          replace
            (fun (acc : N) (t : dtyp) => pad_to_align (IS1.LP.SIZEOF.dtyp_alignment t) acc + IS1.LP.SIZEOF.sizeof_dtyp t)%N with
              (fun (acc : N) (t : dtyp) => pad_to_align (SIZEOF.dtyp_alignment t) acc + SIZEOF.sizeof_dtyp t)%N; eauto.

          apply FunctionalExtensionality.functional_extensionality.
          intros.
          apply FunctionalExtensionality.functional_extensionality.
          intros.
          rewrite sizeof_dtyp_fin_inf.
          rewrite dtyp_alignment_fin_inf.
          auto.
        - replace
            (fun (acc : N) (t : dtyp) => acc + IS1.LP.SIZEOF.sizeof_dtyp t) with
            (fun (acc : N) (t : dtyp) => acc + SIZEOF.sizeof_dtyp t); eauto.

          apply FunctionalExtensionality.functional_extensionality.
          intros.
          apply FunctionalExtensionality.functional_extensionality.
          intros.
          rewrite sizeof_dtyp_fin_inf.
          auto.
      }

      { (* Arrays iptr *)
        cbn in *; rewrite_fin_to_inf_dvalue.
        rewrite H1.
        erewrite IHidxs_fin; eauto.
        rewrite sizeof_dtyp_fin_inf; eauto.
        unfold intptr_fin_inf; break_match_goal; clear Heqs.
        rewrite <- (IS1.LP.IP.from_Z_injective _ _ _ e (IS1.LP.IP.to_Z_from_Z x0)).
        auto.
      }

      { (* Vectors iptr *)
        cbn in *; rewrite_fin_to_inf_dvalue.
        rewrite H1.
        erewrite IHidxs_fin; eauto.
        rewrite sizeof_dtyp_fin_inf; eauto.
        unfold intptr_fin_inf; break_match_goal; clear Heqs.
        rewrite <- (IS1.LP.IP.from_Z_injective _ _ _ e (IS1.LP.IP.to_Z_from_Z x0)).
        auto.
      }
  Qed.

  Lemma handle_gep_addr_fin_inf :
    forall t base_addr_fin base_addr_inf idxs_fin idxs_inf res_addr_fin res_addr_inf,
      GEP.handle_gep_addr t base_addr_fin idxs_fin = inr (NoOom res_addr_fin) ->
      AC2.addr_convert base_addr_fin = NoOom base_addr_inf ->
      AC2.addr_convert res_addr_fin = NoOom res_addr_inf ->
      map fin_to_inf_dvalue idxs_fin = idxs_inf ->
      IS1.LLVM.MEM.MP.GEP.handle_gep_addr t base_addr_inf idxs_inf = inr (NoOom res_addr_inf).
  Proof.
    intros t base_addr_fin base_addr_inf
      idxs_fin idxs_inf res_addr_fin res_addr_inf
      GEP CONV_BASE CONV_RES IDXS.

    destruct idxs_fin.
    - cbn in *; subst; inv GEP.
    - cbn in *; subst; cbn.
      break_inner_match_hyp; inv GEP;
        repeat break_match_hyp_inv;
        rewrite_fin_to_inf_dvalue;
        rewrite sizeof_dtyp_fin_inf;
        erewrite AC2.addr_convert_ptoi in Heqs; eauto;
        eapply handle_gep_h_fin_inf in Heqs; eauto;
        try rewrite Heqs; eauto;
        try erewrite addr_convert_int_to_ptr; eauto.

        unfold intptr_fin_inf; break_inner_match_goal; clear Heqs0.
        rewrite <- (IS1.LP.IP.from_Z_injective _ _ _ e (IS1.LP.IP.to_Z_from_Z x0)).

        setoid_rewrite Heqs.
        erewrite addr_convert_int_to_ptr; eauto.
  Qed.

  Lemma index_into_vec_dv_fin_inf :
    forall t vec idx res,
      @index_into_vec_dv err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) t vec idx = ret res ->
      @IS1.LP.Events.DV.index_into_vec_dv err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) t
        (fin_to_inf_dvalue vec) (fin_to_inf_dvalue idx) =
        ret (fin_to_inf_dvalue res).
  Proof.
    intros t vec idx res INDEX.
    unfold index_into_vec_dv in INDEX.
    unfold IS1.LP.Events.DV.index_into_vec_dv.

    break_match_hyp_inv.
    { (* Arrays *)
      break_match_hyp_inv.
      { (* ix index *)
        generalize dependent res.
        generalize dependent x.
        induction elts; intros x res H0.
        - break_match_hyp_inv;
            unfold fin_to_inf_dvalue;
            try rename p into p';

            break_match_goal;
            break_match_hyp; clear Heqs; destruct p; clear e0;
            cbn in e; inv e; inv H0;

            break_match_goal;
            break_match_hyp; clear Heqs; destruct p; clear e0;
            cbn in e; inv e; inv H0;

            cbn;
            rewrite Heqz;

            break_match_goal; clear Heqs; destruct p; clear e0;
            cbn in e; inv e;

            auto.
        - cbn in H0.
          break_match_hyp_inv.
          + (* Index 0 *)
            clear IHelts.
            unfold fin_to_inf_dvalue.

            break_match_goal;
              break_match_hyp; clear Heqs; destruct p; clear e0;
              cbn in e; inv e;
              break_match_hyp_inv.

            break_match_goal;
              break_match_hyp; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; inv H0.

            destruct (dvalue_convert_strict_fin_inf_succeeds res).
            rewrite e in Heqo.
            cbn.
            rewrite Heqz.
            break_match_hyp_inv.
            cbn.
            break_match_goal; clear Heqs; destruct p.
            rewrite e in e0; inv e0.
            auto.
          + (* Index positive *)
            unfold fin_to_inf_dvalue.
            rename p into p'.

            break_match_goal;
              break_match_hyp; clear Heqs; destruct p; clear e0;
              cbn in e; inv e;
              break_match_hyp_inv;

            break_match_goal;
              break_match_hyp; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; inv H0.

            destruct (dvalue_convert_strict_fin_inf_succeeds res).
            break_match_hyp_inv.
            cbn; rewrite Heqz.
            break_match_hyp_inv.
            cbn.

            subst_existT.
            assert (exists x1, @Integers.signed sz0 x1 = Z.pred (Z.pos p')) as (x1' & X1').
            { exists (repr (Z.pred (Z.pos p'))).
              pose proof (@Integers.min_signed_neg sz0).
              unfold repr.
              cbn.
              rewrite (@Integers.signed_repr sz0); eauto.
              pose proof Integers.signed_range x0.
              break_match_goal; lia.
            }

            specialize (IHelts x1' res).
            forward IHelts.
            { rewrite X1'.
              cbn.
              destruct p'; cbn; auto.
            }

            unfold fin_to_inf_dvalue in IHelts.
            move IHelts after X1'.
            break_match_hyp_inv.
            { move Heqd0 after H0.
              break_match_hyp_inv; clear Heqs; destruct p; clear e1;
              cbn in e0; inv e0.
              break_match_hyp_inv.

              break_match_hyp_inv.
              { move Heqd0 after H2.
                break_match_hyp_inv; clear Heqs; destruct p; clear e1;
                  cbn in e0; inv e0.

                destruct (dvalue_convert_strict_fin_inf_succeeds res).
                rewrite e in e0; inv e0.
                inv H3; subst_existT;
                rewrite X1' in H2.
                rewrite X1'.

                cbn in H2.
                inv Heqo.
                destruct p'; cbn in *; eauto.
              }
            }

            { move Heqd0 after H0;
                break_match_hyp_inv; clear Heqs; destruct p; clear e1;
                cbn in e0;
                break_match_hyp_inv.
              inv H3.
            }
      }
    }

    { (* Vectors *)
      break_match_hyp_inv.
      { (* ix index *)
        generalize dependent res.
        generalize dependent x.
        induction elts; intros x res H0.
        - break_match_hyp_inv;
            unfold fin_to_inf_dvalue;
            try rename p into p';

            break_match_goal;
            break_match_hyp; clear Heqs; destruct p; clear e0;
            cbn in e; inv e; inv H0;

            break_match_goal;
            break_match_hyp; clear Heqs; destruct p; clear e0;
            cbn in e; inv e; inv H0;

            cbn;
            rewrite Heqz;

            break_match_goal; clear Heqs; destruct p; clear e0;
            cbn in e; inv e;

            auto.
        - cbn in H0.
          break_match_hyp_inv.
          + (* Index 0 *)
            clear IHelts.
            unfold fin_to_inf_dvalue.

            break_match_goal;
              break_match_hyp; clear Heqs; destruct p; clear e0;
              cbn in e; inv e;
              break_match_hyp_inv.

            break_match_goal;
              break_match_hyp; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; inv H0.

            destruct (dvalue_convert_strict_fin_inf_succeeds res).
            rewrite e in Heqo.
            cbn.
            rewrite Heqz.
            break_match_hyp_inv.
            cbn.
            break_match_goal; clear Heqs; destruct p.
            rewrite e in e0; inv e0.
            auto.
          + (* Index positive *)
            unfold fin_to_inf_dvalue.
            rename p into p'.

            break_match_goal;
              break_match_hyp; clear Heqs; destruct p; clear e0;
              cbn in e; inv e;
              break_match_hyp_inv;

            break_match_goal;
              break_match_hyp; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; inv H0.

            destruct (dvalue_convert_strict_fin_inf_succeeds res).
            break_match_hyp_inv.
            cbn; rewrite Heqz.
            break_match_hyp_inv.
            cbn.

            subst_existT.
            assert (exists x1, @Integers.signed sz0 x1 = Z.pred (Z.pos p')) as (x1' & X1').
            { exists (repr (Z.pred (Z.pos p'))).
              pose proof (@Integers.min_signed_neg sz0).
              unfold repr.
              cbn.
              rewrite (@Integers.signed_repr sz0); eauto.
              pose proof Integers.signed_range x0.
              break_match_goal; lia.
            }

            specialize (IHelts x1' res).
            forward IHelts.
            { rewrite X1'.
              cbn.
              destruct p'; cbn; auto.
            }

            unfold fin_to_inf_dvalue in IHelts.
            move IHelts after X1'.
            break_match_hyp_inv.

            { move Heqd0 after H0;
                break_match_hyp_inv; clear Heqs; destruct p; clear e1;
                cbn in e0;
                break_match_hyp_inv.
              inv H3.
            }

            { move Heqd0 after H0.
              break_match_hyp_inv; clear Heqs; destruct p; clear e1;
              cbn in e0; inv e0.
              break_match_hyp_inv.

              break_match_hyp_inv.
              { move Heqd0 after H2.
                break_match_hyp_inv; clear Heqs; destruct p; clear e1;
                  cbn in e0; inv e0.

                destruct (dvalue_convert_strict_fin_inf_succeeds res).
                rewrite e in e0; inv e0.
                inv H3; subst_existT;
                rewrite X1' in H2.
                rewrite X1'.

                cbn in H2.
                inv Heqo.
                destruct p'; cbn in *; eauto.
              }
            }
      }
    }
  Qed.

  Lemma insert_into_vec_dv_loop_fin_inf_succeeds :
    forall elts acc idx v res,
      (fix loop (acc elts : list dvalue) (i : LLVMAst.int_ast) {struct elts} :
        option (list dvalue) :=
         match elts with
         | [] => None
         | h :: tl =>
             if (i =? 0)%Z then Some (acc ++ v :: tl) else loop (acc ++ [h]) tl (i - 1)%Z
         end) acc elts idx = ret res ->
      (fix loop (acc elts : list DVCrev.DV2.dvalue) (i : LLVMAst.int_ast) {struct elts} :
        option (list DVCrev.DV2.dvalue) :=
         match elts with
         | [] => None
         | h :: tl =>
             if (i =? 0)%Z then Some (acc ++ (fin_to_inf_dvalue v) :: tl) else loop (acc ++ [h]) tl (i - 1)%Z
         end) (map fin_to_inf_dvalue acc) (map fin_to_inf_dvalue elts) idx = ret (map fin_to_inf_dvalue res).
  Proof.
    induction elts; intros acc idx v res LOOP.
    - discriminate.
    - break_match_hyp_inv.
      + (* Index 0 *)
        cbn. rewrite Heqb.
        rewrite map_app, map_cons.
        reflexivity.
      + destruct elts as [|b elts]; try discriminate.
        cbn. rewrite Heqb.
        break_match_hyp; inv H0.
        -- rewrite map_app, map_cons.
           rewrite map_app.
           reflexivity.
        -- specialize (IHelts (acc ++ [a]) (idx-1)%Z v res).
           rewrite Heqb0 in IHelts.
           specialize (IHelts H1).

           rewrite map_cons in IHelts.
           rewrite Heqb0 in IHelts.
           rewrite map_app in IHelts.
           cbn in IHelts.
           auto.
  Qed.

  Lemma insert_into_vec_dv_loop_fin_inf_fails :
    forall elts acc idx v,
      (fix loop (acc elts : list dvalue) (i : LLVMAst.int_ast) {struct elts} :
        option (list dvalue) :=
         match elts with
         | [] => None
         | h :: tl =>
             if (i =? 0)%Z then Some (acc ++ v :: tl) else loop (acc ++ [h]) tl (i - 1)%Z
         end) acc elts idx = None ->
      (fix loop (acc elts : list DVCrev.DV2.dvalue) (i : LLVMAst.int_ast) {struct elts} :
        option (list DVCrev.DV2.dvalue) :=
         match elts with
         | [] => None
         | h :: tl =>
             if (i =? 0)%Z then Some (acc ++ (fin_to_inf_dvalue v) :: tl) else loop (acc ++ [h]) tl (i - 1)%Z
         end) (map fin_to_inf_dvalue acc) (map fin_to_inf_dvalue elts) idx = None.
  Proof.
    induction elts; intros acc idx v LOOP.
    - cbn; auto.
    - break_match_hyp_inv.
      specialize (IHelts (acc ++ [a]) (idx-1)%Z v H0).
      cbn.
      rewrite Heqb.
      rewrite map_app in IHelts.
      cbn in IHelts.
      auto.
  Qed.

  (* TODO: Move this / generalize monad? *)
  (* TODO: Prove this *)
  Lemma insert_into_vec_dv_fin_inf :
    forall dv1_fin dv2_fin dv3_fin res_fin dv1_inf dv2_inf dv3_inf t,
      @insert_into_vec_dv err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        t dv1_fin dv2_fin dv3_fin = ret res_fin ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      fin_to_inf_dvalue dv3_fin = dv3_inf ->
      @IS1.LP.Events.DV.insert_into_vec_dv err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        t dv1_inf dv2_inf dv3_inf = ret (fin_to_inf_dvalue res_fin).
  Proof.
    intros dv1_fin dv2_fin dv3_fin res_fin dv1_inf dv2_inf dv3_inf t INSERT LIFT1 LIFT2 LIFT3.
    subst.
    unfold insert_into_vec_dv in INSERT.
    unfold IS1.LP.Events.DV.insert_into_vec_dv.

    break_match_hyp_inv.
    { (* Arrays *)
      break_match_hyp_inv.
      { (* ix index *)
        rewrite fin_to_inf_dvalue_array.
        rewrite fin_to_inf_dvalue_ix.
        cbn.
        break_match_hyp_inv.
        - (* Index 0 *)
          break_match_hyp_inv.
          + apply insert_into_vec_dv_loop_fin_inf_succeeds in Heqo.
            setoid_rewrite Heqo; cbn.
            rewrite fin_to_inf_dvalue_array.
            auto.
          + apply insert_into_vec_dv_loop_fin_inf_fails in Heqo.
            setoid_rewrite Heqo; cbn.
            rewrite fin_to_inf_dvalue_poison; auto.
        - (* Index positive *)
          break_match_hyp_inv.
          + apply insert_into_vec_dv_loop_fin_inf_succeeds in Heqo.
            setoid_rewrite Heqo; cbn.
            rewrite fin_to_inf_dvalue_array.
            auto.
          + apply insert_into_vec_dv_loop_fin_inf_fails in Heqo.
            setoid_rewrite Heqo; cbn.
            rewrite fin_to_inf_dvalue_poison; auto.
      }
    }

    { (* Vectors *)
      break_match_hyp_inv.
      { (* ix index *)
        rewrite fin_to_inf_dvalue_vector.
        rewrite fin_to_inf_dvalue_ix.
        cbn.
        break_match_hyp_inv.
        - (* Index 0 *)
          break_match_hyp_inv.
          + apply insert_into_vec_dv_loop_fin_inf_succeeds in Heqo.
            setoid_rewrite Heqo; cbn.
            rewrite fin_to_inf_dvalue_vector.
            auto.
          + apply insert_into_vec_dv_loop_fin_inf_fails in Heqo.
            setoid_rewrite Heqo; cbn.
            rewrite fin_to_inf_dvalue_poison; auto.
        - (* Index positive *)
          break_match_hyp_inv.
          + apply insert_into_vec_dv_loop_fin_inf_succeeds in Heqo.
            setoid_rewrite Heqo; cbn.
            rewrite fin_to_inf_dvalue_vector.
            auto.
          + apply insert_into_vec_dv_loop_fin_inf_fails in Heqo.
            setoid_rewrite Heqo; cbn.
            rewrite fin_to_inf_dvalue_poison; auto.
      }
    }
  Qed.

  Lemma index_into_str_dv_loop_fin_inf :
    forall {elts i res},
      (fix loop elts i :=
         match elts with
         | [] => raise_error "index_into_str_dv: index out of bounds"
         | h :: tl =>
             if (i =? 0)%Z then ret h else loop tl (i-1)%Z
         end) elts i = (res : err_ub_oom dvalue) ->
      (fix loop elts i :=
         match elts with
         | [] => raise_error "index_into_str_dv: index out of bounds"
         | h :: tl =>
             if (i =? 0)%Z then ret h else loop tl (i-1)%Z
         end) (map fin_to_inf_dvalue elts) i = (fmap fin_to_inf_dvalue res : err_ub_oom DVCrev.DV2.dvalue).
  Proof.
    induction elts;
      intros i res LOOP.
    - subst; cbn; auto.
    - break_match_hyp.
      + cbn; rewrite Heqb; inv LOOP.
        reflexivity.
      + apply IHelts in LOOP.
        cbn; rewrite Heqb.
        setoid_rewrite LOOP.
        reflexivity.
  Qed.

  Lemma index_into_str_dv_loop_no_ub_fin_inf :
    forall {elts i ub_msg},
      (fix loop elts i : err_ub_oom dvalue :=
         match elts with
         | [] => raise_error "index_into_str_dv: index out of bounds"
         | h :: tl =>
             if (i =? 0)%Z then ret h else loop tl (i-1)%Z
         end) elts i = UB_unERR_UB_OOM ub_msg -> False.
  Proof.
    induction elts;
      intros i res LOOP; inv LOOP.
    - break_match_hyp; inv H0.
      eapply IHelts; eauto.
  Qed.

  Lemma index_into_str_dv_fin_inf :
    forall {v idx} {res : err_ub_oom dvalue},
      index_into_str_dv v idx = res ->
      E1.DV.index_into_str_dv (fin_to_inf_dvalue v) idx = fmap fin_to_inf_dvalue res.
  Proof.
    intros v idx res H.
    unfold E1.DV.index_into_str_dv, index_into_str_dv in *.
    break_match_hyp;
      try solve
        [ unfold fin_to_inf_dvalue; break_match_goal; break_match_hyp_inv; clear Heqs; destruct p; clear e0;
          cbn in e; inv e;
          cbn; auto; try discriminate
        | unfold fin_to_inf_dvalue; break_match_goal; break_match_hyp_inv; clear Heqs; destruct p; clear e0;
          cbn in e; break_match_hyp_inv;
          cbn; auto; try discriminate
        ].

    - (* Structs *)
      rewrite fin_to_inf_dvalue_struct.
      apply index_into_str_dv_loop_fin_inf; auto.
    - (* Packed Structs *)
      rewrite fin_to_inf_dvalue_packed_struct.
      apply index_into_str_dv_loop_fin_inf; auto.
    - (* Array *)
      rewrite fin_to_inf_dvalue_array.
      apply index_into_str_dv_loop_fin_inf; auto.
  Qed.

  Lemma index_into_str_dv_no_ub_fin_inf :
    forall {v idx ub_msg},
      @index_into_str_dv err_ub_oom _ _ v idx = UB_unERR_UB_OOM ub_msg -> False.
  Proof.
    intros v idx ub_msg H.
    unfold index_into_str_dv in *.
    break_match_hyp; inv H;
      eapply index_into_str_dv_loop_no_ub_fin_inf; eauto.
  Qed.

  Lemma extract_value_loop_fin_inf_succeeds :
    forall idxs str res,
      (fix loop str idxs {struct idxs} : err_ub_oom dvalue :=
         match idxs with
         | [] => ret str
         | i :: tl =>
             v <- index_into_str_dv str i ;;
             loop v tl
         end) str idxs = ret res ->
      (fix loop str idxs {struct idxs} : err_ub_oom DVCrev.DV2.dvalue :=
         match idxs with
         | [] => ret str
         | i :: tl =>
             v <- E1.DV.index_into_str_dv str i ;;
             loop v tl
         end) (fin_to_inf_dvalue str) idxs = ret (fin_to_inf_dvalue res).
  Proof.
    induction idxs;
      intros str res LOOP.
    - inv LOOP; auto.
    - cbn in LOOP.
      repeat break_match_hyp_inv.
      destruct unERR_UB_OOM, unEitherT, unEitherT, unEitherT, unIdent;
        inv Heqs.

      pose proof index_into_str_dv_fin_inf Heqe as INDEX.
      rewrite INDEX.

      match goal with
      | H: EitherMonad.unEitherT
             (EitherMonad.unEitherT
                (EitherMonad.unEitherT
                   (unERR_UB_OOM
                      (?L)))) = _ |- _ =>
          remember L as LOOP
      end.

      destruct_err_ub_oom LOOP; inv H1.
      symmetry in HeqLOOP.
      apply IHidxs in HeqLOOP.

      cbn.
      setoid_rewrite HeqLOOP.
      reflexivity.
  Qed.

  Lemma insert_into_str_loop_fin_inf :
    forall {elts acc v i} {res : err_ub_oom (list dvalue)},
      (fix loop (acc elts:list dvalue) (i:LLVMAst.int_ast) :=
        match elts with
        | [] => raise_error "insert_into_str: index out of bounds"
        | h :: tl =>
          (if i =? 0 then ret (acc ++ (v :: tl))
          else loop (acc ++ [h]) tl (i-1))%Z
        end%list) acc elts i = res ->
      (fix loop (acc elts:list DVCrev.DV2.dvalue) (i:LLVMAst.int_ast) :=
        match elts with
        | [] => raise_error "insert_into_str: index out of bounds"
        | h :: tl =>
          (if i =? 0 then ret (acc ++ ((fin_to_inf_dvalue v) :: tl))
          else loop (acc ++ [h]) tl (i-1))%Z
        end%list) (fmap fin_to_inf_dvalue acc) (fmap fin_to_inf_dvalue elts) i = fmap (fmap fin_to_inf_dvalue) res.
  Proof.
    induction elts;
      intros acc v i res LOOP.
    - subst; cbn; auto.
    - break_match_hyp.
      + cbn; rewrite Heqb; subst; cbn.
        rewrite flat_map_app.
        reflexivity.
      + apply IHelts in LOOP.
        cbn; rewrite Heqb; subst; cbn.
        cbn in LOOP.
        rewrite flat_map_app in LOOP.
        setoid_rewrite LOOP.
        reflexivity.
  Qed.

  (* TODO: Does this not exist somewhere? *)
  Lemma fmap_map :
    forall {A B} (f : A -> B) (l : list A),
      fmap f l = map f l.
  Proof.
    intros A B f l.
    reflexivity.
  Qed.

  Lemma insert_into_str_fin_inf :
    forall {str v i} {res : err_ub_oom dvalue},
      insert_into_str str v i = res ->
      E1.DV.insert_into_str (fin_to_inf_dvalue str) (fin_to_inf_dvalue v) i = fmap fin_to_inf_dvalue res.
  Proof.
    intros str v i res INSERT.
    destruct str;
      try solve
        [ unfold fin_to_inf_dvalue; break_match_goal; clear Heqs; destruct p; clear e0;
          cbn in e; inv e;
          cbn; auto
        | unfold fin_to_inf_dvalue; break_match_goal; clear Heqs; destruct p; clear e0;
          cbn in e; break_match_hyp_inv;
          cbn; auto
        ].

    - (* Structs *)
      rewrite fin_to_inf_dvalue_struct;
        unfold E1.DV.insert_into_str, insert_into_str in *.
      cbn in INSERT.
      break_match_hyp.
      rewrite <- fmap_map.
      apply insert_into_str_loop_fin_inf in Heqe.
      cbn in Heqe.
      cbn.
      setoid_rewrite Heqe.
      subst; cbn.
      destruct unERR_UB_OOM, unEitherT, unEitherT, unEitherT, unIdent;
        inv Heqe; cbn in *; auto.
      destruct s; cbn in *; auto.
      destruct s; cbn in *; auto.

      rewrite fin_to_inf_dvalue_struct.
      reflexivity.
    - (* Packed Structs *)
      rewrite fin_to_inf_dvalue_packed_struct;
        unfold E1.DV.insert_into_str, insert_into_str in *.
      cbn in INSERT.
      break_match_hyp.
      rewrite <- fmap_map.
      apply insert_into_str_loop_fin_inf in Heqe.
      cbn in Heqe.
      cbn.
      setoid_rewrite Heqe.
      subst; cbn.
      destruct unERR_UB_OOM, unEitherT, unEitherT, unEitherT, unIdent;
        inv Heqe; cbn in *; auto.
      destruct s; cbn in *; auto.
      destruct s; cbn in *; auto.

      rewrite fin_to_inf_dvalue_packed_struct.
      reflexivity.
    - (* Array *)
      rewrite fin_to_inf_dvalue_array;
        unfold E1.DV.insert_into_str, insert_into_str in *.
      cbn in INSERT.
      break_match_hyp.
      rewrite <- fmap_map.
      apply insert_into_str_loop_fin_inf in Heqe.
      cbn in Heqe.
      cbn.
      setoid_rewrite Heqe.
      subst; cbn.
      destruct unERR_UB_OOM, unEitherT, unEitherT, unEitherT, unIdent;
        inv Heqe; cbn in *; auto.
      destruct s; cbn in *; auto.
      destruct s; cbn in *; auto.

      rewrite fin_to_inf_dvalue_array.
      reflexivity.
  Qed.

  (* TODO: Move this and consider making err_ub_oom use eq for Eq1... *)
  Lemma err_ub_oom_bind_ret_l_eq :
    forall {A B} (x : A) (k : A -> err_ub_oom B),
      x <- ret x;;
      k x = k x.
  Proof.
    intros A B x k.
    cbn.
    remember (k x) as kx.
    destruct_err_ub_oom kx; auto.
  Qed.

  Lemma insert_value_loop_fin_inf_succeeds :
    forall idxs str elt res,
      (fix loop str idxs : err_ub_oom dvalue :=
         match idxs with
         | [] => raise_error "Index was not provided"
         | i :: nil =>
             v <- insert_into_str str elt i;;
             ret v
         | i :: tl =>
             subfield <- index_into_str_dv str i;;
             modified_subfield <- loop subfield tl;;
             insert_into_str str modified_subfield i
         end) str idxs = res ->
      (fix loop str idxs : err_ub_oom DVCrev.DV2.dvalue :=
         match idxs with
         | [] => raise_error "Index was not provided"
         | i :: nil =>
             v <- E1.DV.insert_into_str str (fin_to_inf_dvalue elt) i;;
             ret v
         | i :: tl =>
             subfield <- E1.DV.index_into_str_dv str i;;
             modified_subfield <- loop subfield tl;;
             E1.DV.insert_into_str str modified_subfield i
         end) (fin_to_inf_dvalue str) idxs = fmap fin_to_inf_dvalue res.
  Proof.
    induction idxs;
      intros str elt res LOOP.
    - subst; auto.
    - break_match_hyp.
      + cbn in *.
        break_match_hyp.
        remember (insert_into_str str elt a) as insert.
        symmetry in Heqinsert.
        pose proof insert_into_str_fin_inf Heqinsert as Heqinsert'.
        rewrite Heqinsert'.
        destruct_err_ub_oom insert; subst; inv Heqe; cbn in *;
          auto.
      + remember (index_into_str_dv str a) as index.
        symmetry in Heqindex.
        pose proof index_into_str_dv_fin_inf Heqindex as Hindex.
        rewrite Hindex.

        destruct_err_ub_oom index;
          try solve [subst; cbn in *; auto].

        rename index0 into subf.
        cbn in LOOP.
        break_match_hyp.
        apply IHidxs in Heqe.

        setoid_rewrite err_ub_oom_bind_ret_l_eq.
        rewrite Heqe.
        destruct unERR_UB_OOM, unEitherT, unEitherT, unEitherT, unIdent.
        { subst; inv Heqe; cbn in *; auto. }
        destruct s.
        { subst; inv Heqe; cbn in *; auto. }
        destruct s.
        { subst; inv Heqe; cbn in *; auto. }

        setoid_rewrite err_ub_oom_bind_ret_l_eq.
        apply insert_into_str_fin_inf.
        subst; cbn in *.
        remember (insert_into_str str d a) as insert.
        destruct_err_ub_oom insert; auto.
  Qed.

  Import CONCBASE.
  Lemma eval_select_cond_fin_inf :
    forall a d d0 x,
      match a with
      | @DVALUE_I 1 i =>
          if (@Integers.unsigned 1 i =? 1)%Z
          then fun y : err_ub_oom dvalue => success_unERR_UB_OOM d = y
          else fun y : err_ub_oom dvalue => success_unERR_UB_OOM d0 = y
      | DVALUE_Poison t => fun y : err_ub_oom dvalue => success_unERR_UB_OOM (DVALUE_Poison t) = y
      | _ =>
          fun ue : err_ub_oom dvalue =>
            ERR_unERR_UB_OOM
              "concretize_uvalueM: ill-typed select, condition in vector was not poison or i1." = ue
      end x ->
      match fin_to_inf_dvalue a with
      | @E1.DV.DVALUE_I 1 i =>
          if (@Integers.unsigned 1 i =? 1)%Z
          then fun y : err_ub_oom DVCrev.DV2.dvalue => success_unERR_UB_OOM (fin_to_inf_dvalue d) = y
          else fun y : err_ub_oom DVCrev.DV2.dvalue => success_unERR_UB_OOM (fin_to_inf_dvalue d0) = y
      | E1.DV.DVALUE_Poison t => fun y : err_ub_oom DVCrev.DV2.dvalue => success_unERR_UB_OOM (E1.DV.DVALUE_Poison t) = y
      | _ =>
          fun ue : err_ub_oom DVCrev.DV2.dvalue =>
            ERR_unERR_UB_OOM
              "concretize_uvalueM: ill-typed select, condition in vector was not poison or i1." = ue
      end (fmap fin_to_inf_dvalue x).
  Proof.
    intros a d d0 x H.
    destruct a; subst.

    all:
      try solve
        [ unfold fin_to_inf_dvalue; break_match_goal; cbn; auto;
          break_match_hyp; clear Heqs; destruct p; clear e0;
          subst; cbn in e; inv e
        | unfold fin_to_inf_dvalue; break_match_goal; cbn; auto;
          break_match_hyp; clear Heqs; destruct p; clear e0;
          subst; cbn in e; break_match_hyp_inv
        ].

    { (* i1 *)
      rewrite_fin_to_inf_dvalue.
      break_match_hyp; subst; cbn; auto.
      break_match_hyp; subst; cbn; auto.
    }

    { (* Poison *)
      rewrite fin_to_inf_dvalue_poison.
      cbn.
      rewrite fin_to_inf_dvalue_poison.
      reflexivity.
    }
  Qed.

  Lemma eval_select_loop_fin_inf :
    forall (conds xs ys : list dvalue) (res : err_ub_oom (list dvalue)),
      (fix loop conds xs ys {struct conds} : ErrUbOomProp (list dvalue) :=
         match conds, xs, ys with
         | [], [], [] => @ret ErrUbOomProp Monad_ErrUbOomProp _ []
         | (c::conds), (x::xs), (y::ys) =>
             @bind ErrUbOomProp Monad_ErrUbOomProp _ _
               (match c with
                | DVALUE_Poison t =>
                    (* TODO: Should be the type of the result of the select... *)
                    @ret ErrUbOomProp Monad_ErrUbOomProp _ (DVALUE_Poison t)
                | @DVALUE_I 1 i =>
                    if (@Integers.unsigned 1 i =? 1)%Z
                    then @ret ErrUbOomProp Monad_ErrUbOomProp _ x
                    else @ret ErrUbOomProp Monad_ErrUbOomProp _ y
                | _ =>
                    fun ue =>
                      (raise_error "concretize_uvalueM: ill-typed select, condition in vector was not poison or i1." = ue)
                end)
               (fun selected =>
                  @bind ErrUbOomProp Monad_ErrUbOomProp _ _
                    (loop conds xs ys)
                    (fun rest =>
                       @ret ErrUbOomProp Monad_ErrUbOomProp _ (selected :: rest)))
         | _, _, _ =>
             fun ue => (raise_error "concretize_uvalueM: ill-typed vector select, length mismatch." = ue)
         end) conds xs ys res ->
      (fix loop conds xs ys {struct conds} : ErrUbOomProp (list DVCrev.DV2.dvalue) :=
         match conds, xs, ys with
         | [], [], [] => @ret ErrUbOomProp Monad_ErrUbOomProp _ []
         | (c::conds), (x::xs), (y::ys) =>
             @bind ErrUbOomProp Monad_ErrUbOomProp _ _
               (match c with
                | IS1.LP.Events.DV.DVALUE_Poison t =>
                    (* TODO: Should be the type of the result of the select... *)
                    @ret ErrUbOomProp Monad_ErrUbOomProp _ (IS1.LP.Events.DV.DVALUE_Poison t)
                | @IS1.LP.Events.DV.DVALUE_I 1 i =>
                    if (@Integers.unsigned 1 i =? 1)%Z
                    then @ret ErrUbOomProp Monad_ErrUbOomProp _ x
                    else @ret ErrUbOomProp Monad_ErrUbOomProp _ y
                | _ =>
                    fun ue =>
                      (raise_error "concretize_uvalueM: ill-typed select, condition in vector was not poison or i1." = ue)
                end)
               (fun selected =>
                  @bind ErrUbOomProp Monad_ErrUbOomProp _ _
                    (loop conds xs ys)
                    (fun rest =>
                       @ret ErrUbOomProp Monad_ErrUbOomProp _ (selected :: rest)))
         | _, _, _ =>
             fun ue => (raise_error "concretize_uvalueM: ill-typed vector select, length mismatch." = ue)
         end) (map fin_to_inf_dvalue conds) (map fin_to_inf_dvalue xs) (map fin_to_inf_dvalue ys) (fmap (map fin_to_inf_dvalue) res).
  Proof.
    induction conds, xs, ys;
      intros res LOOP;
      cbn in *; subst; auto.

    repeat red in LOOP.
    destruct LOOP as (?&?&?&?&?).
    repeat red.

    exists (fmap fin_to_inf_dvalue x).
    exists (fun _ => fmap (fmap fin_to_inf_dvalue) res).
    split.
    apply (eval_select_cond_fin_inf _ _ _ _ H).
    split.
    subst; cbn.
    { destruct_err_ub_oom x; cbn; auto. }

    destruct_err_ub_oom x; cbn; auto.
    right; intros a0 ?; subst.
    repeat red.

    destruct H1 as [[] | H1].
    specialize (H1 _ eq_refl).

    repeat red in H1.
    destruct H1 as (?&?&?&?&?).

    pose proof H0 as LOOP.
    eapply IHconds in LOOP.
    exists ({|
             unERR_UB_OOM :=
               {|
                 EitherMonad.unEitherT :=
                   {|
                     EitherMonad.unEitherT :=
                       {|
                         EitherMonad.unEitherT :=
                           match
                             IdentityMonad.unIdent
                               (EitherMonad.unEitherT
                                  (EitherMonad.unEitherT (EitherMonad.unEitherT (unERR_UB_OOM x))))
                           with
                           | inl x => {| IdentityMonad.unIdent := inl x |}
                           | inr x =>
                               EitherMonad.unEitherT
                                 match x with
                                 | inl x0 =>
                                     {|
                                       EitherMonad.unEitherT :=
                                         {| IdentityMonad.unIdent := inr (inl x0) |}
                                     |}
                                 | inr x0 =>
                                     EitherMonad.unEitherT
                                       match x0 with
                                       | inl x1 =>
                                           {|
                                             EitherMonad.unEitherT :=
                                               {|
                                                 EitherMonad.unEitherT :=
                                                   {| IdentityMonad.unIdent := inr (inr (inl x1)) |}
                                               |}
                                           |}
                                       | inr x1 =>
                                           {|
                                             EitherMonad.unEitherT :=
                                               {|
                                                 EitherMonad.unEitherT :=
                                                   {|
                                                     IdentityMonad.unIdent :=
                                                       inr (inr (inr (map fin_to_inf_dvalue x1)))
                                                   |}
                                               |}
                                           |}
                                       end
                                 end
                           end
                       |}
                   |}
               |}
        |}).
    exists (fun elts => fmap (fmap fin_to_inf_dvalue) (x0 x1)).
    { destruct_err_ub_oom x; cbn; rewrite <- H1; cbn; auto.
      split; eauto.
      cbn in H1.
      split; eauto.

      right; intros ??; subst.
      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).
      rewrite <- H2.
      cbn.

      reflexivity.
    }
  Qed.

  Lemma eval_select_fin_inf :
    forall cond uv1_fin uv2_fin uv1_inf uv2_inf res
      (IH1 : forall dv_fin : dvalue,
          IS2.MEM.CP.CONC.concretize uv1_fin dv_fin ->
          IS1.MEM.CP.CONC.concretize uv1_inf (fin_to_inf_dvalue dv_fin))
      (IH2 : forall dv_fin : dvalue,
          IS2.MEM.CP.CONC.concretize uv2_fin dv_fin ->
          IS1.MEM.CP.CONC.concretize uv2_inf (fin_to_inf_dvalue dv_fin)),
      @eval_select ErrUbOomProp Monad_ErrUbOomProp
        (fun (dt : dtyp) (edv : err_ub_oom dvalue) =>
           match unERR_UB_OOM edv with
           | {|
               EitherMonad.unEitherT :=
                 {|
                   EitherMonad.unEitherT :=
                     {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |}
                 |}
             |} => dvalue_has_dtyp dv dt /\ dv <> DVALUE_Poison dt
           | _ => True
           end) err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (fun (A : Type) (x ue : err_ub_oom A) => x = ue) cond uv1_fin uv2_fin (ret res) ->
      @IS1.MEM.CP.CONC.eval_select ErrUbOomProp Monad_ErrUbOomProp
        (fun (dt : dtyp) (edv : err_ub_oom DVCrev.DV2.dvalue) =>
           match unERR_UB_OOM edv with
           | {|
               EitherMonad.unEitherT :=
                 {|
                   EitherMonad.unEitherT :=
                     {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |}
                 |}
             |} => E1.DV.dvalue_has_dtyp dv dt /\ dv <> E1.DV.DVALUE_Poison dt
           | _ => True
           end) err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (fun (A : Type) (x ue : err_ub_oom A) => x = ue) (fin_to_inf_dvalue cond) uv1_inf uv2_inf (fmap fin_to_inf_dvalue (ret res)).
  Proof.
    intros cond uv1_fin uv2_fin uv1_inf uv2_inf res IH1 IH2 EVAL.
    destruct cond.
    { unfold fin_to_inf_dvalue at 1.
      break_match_goal; clear Heqs; destruct p; clear e0;
      cbn in e; break_match_hyp_inv;
        cbn in *; subst; cbn in *; auto; inv EVAL.
    }

    { (* i1 conditional *)
      rewrite eval_select_equation in *.
      rewrite IS1.MEM.CP.CONC.eval_select_equation.
      rewrite fin_to_inf_dvalue_ix.

      break_match; try inv EVAL.
      break_match.
      - eapply IH1; eauto.
      - eapply IH2; eauto.
    }

    all: try solve
           [ unfold fin_to_inf_dvalue at 1;
             break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e;
             cbn in *; subst; cbn in *; inv EVAL; auto
           | unfold fin_to_inf_dvalue at 1;
             break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e;
             cbn in *; subst; cbn in *; reflexivity
           | unfold fin_to_inf_dvalue at 1;
             break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; break_match_hyp_inv;
             cbn in *; subst; cbn in *; auto; inv EVAL
           ].

    { (* Poison *)
      rewrite fin_to_inf_dvalue_poison.
      cbn in *; subst; cbn; inv EVAL.
      rewrite fin_to_inf_dvalue_poison.
      reflexivity.
    }

    { (* Vector conditional *)
      rewrite eval_select_equation in *.
      rewrite IS1.MEM.CP.CONC.eval_select_equation.

      repeat red in EVAL.
      destruct EVAL as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      destruct H1 as [[] | H1].
      specialize (H1 _ eq_refl).

      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.
      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).

      destruct x1;
        try (rewrite <- H2 in H5; inv H5).
      { (* Poison *)
        rewrite fin_to_inf_dvalue_vector.
        cbn.
        repeat red.

        exists (ret (fin_to_inf_dvalue (DVALUE_Poison t0))).
        exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 (DVALUE_Poison t0)))).

        split.
        eapply IH1; eauto.

        split.
        cbn in *; rewrite <- H2 in H1; inv H1; cbn.
        auto.

        right; intros ? ?; subst.
        repeat red.
        cbn in *.
        rewrite <- H2 in H1.
        cbn in H1.
        subst.

        exists (ret (fin_to_inf_dvalue x3)).
        exists (fun _ => (fmap fin_to_inf_dvalue (x2 x3))).
        cbn; rewrite <- H2, <- H1; cbn.

        split.
        eapply IH2; eauto.

        split; eauto.
        right; intros ? ?; subst.
        rewrite fin_to_inf_dvalue_poison.
        reflexivity.
      }

      (* Vector *)
      destruct x3;
        try (rewrite <- H2 in H5; inv H5).
      { (* Poison *)
        rewrite fin_to_inf_dvalue_vector.
        cbn.
        repeat red.

        exists (ret (fin_to_inf_dvalue (DVALUE_Vector t0 elts0))).
        exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 (DVALUE_Vector t0 elts0)))).

        split.
        eapply IH1; eauto.

        split.
        cbn in *; rewrite <- H2 in H1; inv H1; cbn.
        auto.

        right; intros ? ?; subst.
        repeat red.
        cbn in *.
        rewrite <- H2 in H1.
        cbn in H1.
        subst.

        exists (ret (fin_to_inf_dvalue (DVALUE_Poison t1))).
        exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 (DVALUE_Poison t1)))).

        split.
        eapply IH2; eauto.

        rewrite fin_to_inf_dvalue_poison, <- H2, <- H1; cbn.
        split; eauto.
        right; intros ? ?; subst.
        rewrite fin_to_inf_dvalue_vector, fin_to_inf_dvalue_poison.
        reflexivity.
      }

      repeat red in H2.
      destruct H2 as (?&?&?&?&?).

      rename elts0 into elts1_fin.
      rename elts1 into elts2_fin.
      pose proof (eval_select_loop_fin_inf elts elts1_fin elts2_fin x H2) as EVAL.

      subst.
      rewrite fin_to_inf_dvalue_vector.
      cbn.

      pose proof (IH1 _ H) as IHelts1.
      pose proof (IH2 _ H0) as IHelts2.

      cbn in H1.
      remember (x2 (DVALUE_Vector t1 elts2_fin)) as x2elts.
      destruct_err_ub_oom x2elts; inv H5.
      cbn in H1.

      repeat red.
      exists (ret (fin_to_inf_dvalue (DVALUE_Vector t0 elts1_fin))).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 (DVALUE_Vector t0 elts1_fin)))).
      cbn; rewrite <- H1; cbn.
      split; eauto.
      split; eauto.

      right; intros a ?; subst.
      repeat red.
      exists (ret (fin_to_inf_dvalue (DVALUE_Vector t1 elts2_fin))).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 (DVALUE_Vector t1 elts2_fin)))).
      cbn; rewrite <- Heqx2elts; cbn.
      split; eauto.
      split; eauto.

      right; intros a ?; subst.
      do 2 rewrite fin_to_inf_dvalue_vector.
      repeat red.
      exists (fmap (map fin_to_inf_dvalue) x).
      exists (fun elts => ret (IS1.LP.Events.DV.DVALUE_Vector t0 elts)).
      split; eauto.
      split; eauto.

      destruct_err_ub_oom x; inv H3.
      destruct H4 as [[] | H4].
      specialize (H4 _ eq_refl).
      rewrite <- H4 in H6.
      inv H6.
      cbn.
      rewrite fin_to_inf_dvalue_vector.
      reflexivity.
    }
  Qed.

  (* TODO: Move this *)
  Lemma fin_to_inf_dvalue_not_poison :
    forall dv_fin t,
      dv_fin <> DVALUE_Poison t ->
      fin_to_inf_dvalue dv_fin <> IS1.LP.Events.DV.DVALUE_Poison t.
  Proof.
    intros dv_fin t NPOISON CONTRA.
    eapply NPOISON.
    destruct dv_fin; cbn in CONTRA;
      unfold fin_to_inf_dvalue in *;
      break_match_hyp_inv; subst_existT; clear Heqs; destruct p; clear e0;
      cbn in *;
      try break_match_hyp_inv; try inv e; try discriminate.
    inv H1.
    auto.
  Qed.

  Definition concretization_list_refine : (list (IS1.LP.Events.DV.uvalue * IS1.LP.Events.DV.dvalue)) -> (list (uvalue * dvalue)) -> Prop
    :=
    Forall2 (uvalue_refine_strict × dvalue_refine_strict).

  Definition concretization_map_refine
    (inf_map : NMap (list (IS1.LP.Events.DV.uvalue * IS1.LP.Events.DV.dvalue)))
    (fin_map : NMap (list (uvalue * dvalue))) : Prop
    :=
    NM_Refine concretization_list_refine inf_map fin_map.

  Lemma concretization_map_refine_empty :
    concretization_map_refine (NM.empty (list (IS1.LP.Events.DV.uvalue * IS1.LP.Events.DV.dvalue))) (NM.empty (list (uvalue * dvalue))).
  Proof.
    repeat red.
    split.
    - intros k.
      split; intros CONTRA;
        eapply NM_In_empty_contra in CONTRA; contradiction.
    - intros k e e' H H0.
      repeat red in H.
      eapply NM.Raw.Proofs.empty_1 in H; contradiction.
  Qed.

  Lemma concretize_map_refine_find_none_inf_fin :
    forall acc_inf acc_fin sid,
      concretization_map_refine acc_inf acc_fin ->
      NM.find (elt:=list (IS1.LP.Events.DV.uvalue * IS1.LP.Events.DV.dvalue)) sid acc_inf = None ->
      NM.find (elt:=list (uvalue * dvalue)) sid acc_fin = None.
  Proof.
    intros acc_inf acc_fin sid ACC_REF FIND.
    destruct (NM.find (elt:=list (uvalue * dvalue)) sid acc_fin) eqn:FIND_FIN; auto.
    exfalso.

    destruct ACC_REF as (ACC_IN & ACC_MAPSTO).
    apply NM_find_In in FIND_FIN.
    apply ACC_IN in FIND_FIN.
    apply NM_find_not_In in FIND.
    contradiction.
  Qed.

  Lemma concretize_map_refine_find_some_inf_fin :
    forall acc_inf acc_fin sid conc_list_inf,
      concretization_map_refine acc_inf acc_fin ->
      NM.find (elt:=list (IS1.LP.Events.DV.uvalue * IS1.LP.Events.DV.dvalue)) sid acc_inf = Some conc_list_inf ->
      exists conc_list_fin,
        NM.find (elt:=list (uvalue * dvalue)) sid acc_fin = Some conc_list_fin /\
          concretization_list_refine conc_list_inf conc_list_fin.
  Proof.
    intros acc_inf acc_fin sid conc_list_inf ACC_REF FIND.
    destruct ACC_REF as (ACC_IN & ACC_MAPSTO).
    pose proof FIND as IN.
    apply NM_find_In in IN.
    apply ACC_IN in IN.
    destruct IN.
    exists x.
    apply NM.find_2 in FIND.
    split.
    - apply NM.find_1; auto.
    - eapply ACC_MAPSTO; eauto.
  Qed.

  Lemma concretize_map_refine_new_concretized_byte_fin_inf :
    forall acc_inf acc_fin uv_inf uv_fin dv_inf dv_fin sid,
      concretization_map_refine acc_inf acc_fin ->
      uvalue_refine_strict uv_inf uv_fin ->
      dvalue_refine_strict dv_inf dv_fin ->
      concretization_map_refine
        (IS1.LLVM.MEM.CP.CONCBASE.new_concretized_byte acc_inf uv_inf dv_inf sid)
        (new_concretized_byte acc_fin uv_fin dv_fin sid).
  Proof.
    intros acc_inf acc_fin uv_inf uv_fin dv_inf dv_fin
      sid ACC_REF UV_REF DV_REF.
    repeat red.
    split.
    { (* In *)
      intros k.
      unfold IS1.LLVM.MEM.CP.CONCBASE.new_concretized_byte,
        new_concretized_byte in *.
      split; intros IN.
      - break_match_hyp.
        + eapply concretize_map_refine_find_some_inf_fin in Heqo; eauto.
          destruct Heqo as (?&?&?).
          rewrite H.
          break_match_hyp.
          * eapply assoc_similar_lookup in Heqo.
            3: apply H0.
            2: apply uvalue_refine_strict_R2_injective.
            destruct Heqo as (?&?&?&?&?&?).
            assert (x0 = uv_fin).
            { pose proof Util.Forall2_Nth H2 H3 H0.
              destruct H4.
              cbn in *.
              red in UV_REF, fst_rel.
              rewrite UV_REF in fst_rel.
              inv fst_rel; auto.
            }
            subst.

            rewrite H1.
            apply ACC_REF; auto.
          * assert (Util.assoc uv_fin x = None).
            { eapply assoc_similar_no_lookup
                with (xs:=l); eauto.
              apply uvalue_refine_strict_R2_injective.
            }
            rewrite H1.

            assert ((k = sid) \/ (k <> sid)) as [EQ | NEQ] by lia.
            -- subst.
               apply NM_In_add_eq.
            -- apply NM_In_add_neq; eauto.
               apply NM_In_add_neq in IN; eauto.
               apply ACC_REF; auto.
        + eapply concretize_map_refine_find_none_inf_fin in Heqo; eauto.
          rewrite Heqo.

          assert ((k = sid) \/ (k <> sid)) as [EQ | NEQ] by lia.
          -- subst.
             apply NM_In_add_eq.
          -- apply NM_In_add_neq; eauto.
             apply NM_In_add_neq in IN; eauto.
             apply ACC_REF; auto.
      - break_match_goal.
        + eapply concretize_map_refine_find_some_inf_fin in Heqo; eauto.
          destruct Heqo as (?&?&?).
          rewrite H in IN.
          break_match_goal.
          * eapply assoc_similar_lookup in Heqo.
            3: apply H0.
            2: apply uvalue_refine_strict_R2_injective.
            destruct Heqo as (?&?&?&?&?&?).
            assert (x0 = uv_fin).
            { pose proof Util.Forall2_Nth H2 H3 H0.
              destruct H4.
              cbn in *.
              red in UV_REF, fst_rel.
              rewrite UV_REF in fst_rel.
              inv fst_rel; auto.
            }
            subst.

            rewrite H1 in IN.
            apply ACC_REF; auto.
          * assert (Util.assoc uv_fin x = None).
            { eapply assoc_similar_no_lookup
                with (xs:=l); eauto.
              apply uvalue_refine_strict_R2_injective.
            }
            rewrite H1 in IN.

            assert ((k = sid) \/ (k <> sid)) as [EQ | NEQ] by lia.
            -- subst.
               apply NM_In_add_eq.
            -- apply NM_In_add_neq; eauto.
               apply NM_In_add_neq in IN; eauto.
               apply ACC_REF; auto.
        + eapply concretize_map_refine_find_none_inf_fin in Heqo; eauto.
          rewrite Heqo in IN.

          assert ((k = sid) \/ (k <> sid)) as [EQ | NEQ] by lia.
          -- subst.
             apply NM_In_add_eq.
          -- apply NM_In_add_neq; eauto.
             apply NM_In_add_neq in IN; eauto.
             apply ACC_REF; auto.
    }

    { (* MapsTo *)
      intros k e e' MAPS1 MAPS2.
      unfold IS1.LLVM.MEM.CP.CONCBASE.new_concretized_byte,
        new_concretized_byte in *.
      red.
      pose proof ACC_REF as [_ ACC_MAPS].
      destruct (NM.find (elt:=list (IS1.LP.Events.DV.uvalue * IS1.LP.Events.DV.dvalue)) sid acc_inf) eqn:FIND_INF.
      - eapply concretize_map_refine_find_some_inf_fin in FIND_INF; eauto.
        destruct FIND_INF as (?&?&?).
        rewrite H in MAPS2.
        destruct (Util.assoc uv_inf l) eqn:ASSOC.
        + eapply assoc_similar_lookup
            with (xs:=l) in ASSOC; eauto.
          2: apply uvalue_refine_strict_R2_injective.

          destruct ASSOC as (?&?&?&?&?&?).
          assert (x0 = uv_fin).
          { pose proof Util.Forall2_Nth H2 H3 H0.
            destruct H4.
            cbn in *.
            red in UV_REF, fst_rel.
            rewrite UV_REF in fst_rel.
            inv fst_rel; auto.
          }
          subst.
          rewrite H1 in MAPS2.
          eapply ACC_MAPS; eauto.
        + assert (Util.assoc uv_fin x = None).
          { eapply assoc_similar_no_lookup
              with (xs:=l); eauto.
            apply uvalue_refine_strict_R2_injective.
          }
          rewrite H1 in MAPS2.

          assert ((k = sid) \/ (k <> sid)) as [EQ | NEQ] by lia.
          -- subst.
             apply NM_MapsTo_eq in MAPS1, MAPS2; subst.
             apply Forall2_app; auto.
          -- apply NM.add_3 in MAPS1, MAPS2; auto.
             eapply ACC_MAPS; eauto.
      - eapply concretize_map_refine_find_none_inf_fin in FIND_INF; eauto.
        rewrite FIND_INF in MAPS2.
        assert ((k = sid) \/ (k <> sid)) as [EQ | NEQ] by lia.
        -- subst.
           apply NM_MapsTo_eq in MAPS1, MAPS2; subst.
           repeat constructor; cbn; auto.
        -- apply NM.add_3 in MAPS1, MAPS2; auto.
           eapply ACC_MAPS; eauto.
    }
  Qed.

  Lemma pre_concretized_fin_inf :
    forall uv_inf uv_fin acc_inf acc_fin sid,
      concretization_map_refine acc_inf acc_fin ->
      uvalue_refine_strict uv_inf uv_fin ->
      IS1.LLVM.MEM.CP.CONCBASE.pre_concretized acc_inf uv_inf sid =
        fmap fin_to_inf_dvalue (pre_concretized acc_fin uv_fin sid).
  Proof.
    intros uv_inf uv_fin acc_inf acc_fin sid ACC_REF REF.
    unfold pre_concretized,
      IS1.LLVM.MEM.CP.CONCBASE.pre_concretized.
    cbn.
    break_match_goal.
    - eapply concretize_map_refine_find_some_inf_fin in Heqo;
        eauto.
      destruct Heqo as (?&?&?).
      rewrite H.
      destruct (Util.assoc uv_inf l) eqn:ASSOC.
      + eapply assoc_similar_lookup
            with (xs:=l) in ASSOC; eauto.
        2: apply uvalue_refine_strict_R2_injective.

        destruct ASSOC as (?&?&?&?&?&?).
        pose proof Util.Forall2_Nth H2 H3 H0.
        destruct H4; cbn in *.
        red in REF, fst_rel.
        rewrite REF in fst_rel.
        inv fst_rel; auto.

        rewrite H1.
        erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
      + assert (Util.assoc uv_fin x = None).
        { eapply assoc_similar_no_lookup
            with (xs:=l); eauto.
          apply uvalue_refine_strict_R2_injective.
        }
        rewrite H1; auto.
    - eapply concretize_map_refine_find_none_inf_fin in Heqo;
        eauto.
      rewrite Heqo.
      auto.
  Qed.

  Lemma concretize_uvalue_bytes_helper_fin_inf :
    forall uvs_inf uvs_fin acc_inf acc_fin res
      (IH : forall (u : DV1.uvalue),
          Exists (DV1.uvalue_subterm u) uvs_inf ->
          forall uv_fin : DV2.uvalue,
            uvalue_refine_strict u uv_fin ->
            forall dv_fin : dvalue,
              IS2.MEM.CP.CONC.concretize uv_fin dv_fin ->
              IS1.MEM.CP.CONC.concretize u (fin_to_inf_dvalue dv_fin)),
      Forall2 uvalue_refine_strict uvs_inf uvs_fin ->
      concretization_map_refine acc_inf acc_fin ->
      @concretize_uvalue_bytes_helper ErrUbOomProp Monad_ErrUbOomProp
        (fun (dt : dtyp) (edv : err_ub_oom dvalue) =>
           match @unERR_UB_OOM IdentityMonad.ident dvalue edv with
           | {|
               EitherMonad.unEitherT :=
                 {|
                   EitherMonad.unEitherT :=
                     {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |}
                 |}
             |} => dvalue_has_dtyp dv dt /\ dv <> DVALUE_Poison dt
           | _ => True
           end) err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (fun (A : Type) (x ue : err_ub_oom A) => x = ue) acc_fin uvs_fin (ret res) ->
      @IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalue_bytes_helper ErrUbOomProp Monad_ErrUbOomProp
        (fun (dt0 : dtyp) (edv : err_ub_oom IS1.LP.Events.DV.dvalue) =>
           match @unERR_UB_OOM IdentityMonad.ident IS1.LP.Events.DV.dvalue edv with
           | {|
               EitherMonad.unEitherT :=
                 {|
                   EitherMonad.unEitherT :=
                     {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |}
                 |}
             |} => IS1.LP.Events.DV.dvalue_has_dtyp dv dt0 /\ dv <> IS1.LP.Events.DV.DVALUE_Poison dt0
           | _ => True
           end) err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (fun (A : Type) (x ue : err_ub_oom A) => x = ue) acc_inf uvs_inf (ret (map fin_to_inf_dvalue_byte res)).
  Proof.
    (* Will need something about acc_inf and acc_fin *)
    induction uvs_inf;
      intros uvs_fin acc_inf acc_fin res IH REF ACC_REF CONC.
    - inv REF.
      cbn in CONC; inv CONC; cbn.
      reflexivity.
    - inv REF.
      rewrite concretize_uvalue_bytes_helper_equation in CONC.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalue_bytes_helper_equation.
      destruct y; uvalue_refine_strict_inv H1; try inv CONC.
      rewrite pre_concretized_fin_inf with (uv_fin:=y) (acc_fin:=acc_fin); eauto.
      break_match_hyp_inv; repeat red.
      + (* pre-concretization exists *)
        destruct H as (?&?&?&?).
        destruct_err_ub_oom x0; inv H1.
        destruct H2 as [[] | H2].
        specialize (H2 x2).
        forward H2; [cbn; auto|].
        cbn in H2.
        rewrite <- H2 in H5.
        inv H5.

        specialize (IHuvs_inf l' acc_inf acc_fin x2).
        repeat (forward IHuvs_inf; eauto).

        exists (ret (map fin_to_inf_dvalue_byte x2)).
        exists (fun _ => ret (map fin_to_inf_dvalue_byte (DVALUE_ExtractByte d dt idx :: x2))).
        split; eauto.
        split; eauto.

        right.
        intros a RETa.
        inv RETa.
        cbn.
        reflexivity.
      + (* No pre-concretization exists *)
        destruct H as (?&?&?&?).
        destruct_err_ub_oom x0; inv H1.
        destruct H2 as [[] | H2].
        specialize (H2 x2).
        forward H2; [cbn; auto|].
        cbn in H2.
        repeat red in H2.
        destruct H2 as (?&?&?&?&?).
        rewrite <- H2 in H5.
        destruct_err_ub_oom x0; inv H5.
        destruct H4 as [[] | H4].
        specialize (H4 x4).
        forward H4; [cbn; auto|].
        rewrite <- H4 in H7.
        inv H7.

        eapply IH in H; eauto.
        2: solve [repeat constructor].
        exists (ret (fin_to_inf_dvalue x2)).
        exists (fun _ => ret (map fin_to_inf_dvalue_byte (DVALUE_ExtractByte x2 dt idx :: x4))).
        split; eauto.
        split; eauto.

        right.
        intros a RETa.
        inv RETa.
        cbn in H2.
        rewrite <- H4 in H2.
        inv H2.
        repeat red.

        specialize
          (IHuvs_inf l'
             (IS1.LLVM.MEM.CP.CONCBASE.new_concretized_byte acc_inf x (fin_to_inf_dvalue x2) sid)
             (new_concretized_byte acc_fin y x2 sid) x4).
        forward IHuvs_inf; eauto.
        forward IHuvs_inf; eauto.
        forward IHuvs_inf.
        eapply concretize_map_refine_new_concretized_byte_fin_inf; eauto.
        apply fin_to_inf_dvalue_refine_strict.
        forward IHuvs_inf; eauto.

        exists (ret (map fin_to_inf_dvalue_byte x4)).
        exists (fun _ =>
             ret (map fin_to_inf_dvalue_byte (DVALUE_ExtractByte x2 dt idx :: x4))).
        split; eauto.
        split; eauto.

        right.
        intros a RETa.
        inv RETa.
        cbn.
        reflexivity.
  Qed.

  Lemma dvalue_int_unsigned_E1E2 :
    forall x y,
      dvalue_refine_strict x y ->
      IS1.LP.Events.DV.dvalue_int_unsigned x = dvalue_int_unsigned y.
  Proof.
    induction x; intros y REF;
      try
        solve
        [ unfold dvalue_refine_strict in *;
          cbn in *; inv REF; cbn; auto
        | unfold dvalue_refine_strict in *;
          cbn in *;
          break_match_hyp; inv REF;
          cbn; auto
        ].
    - unfold dvalue_refine_strict in *.
      cbn in *.
      break_match_hyp_inv.
      unfold dvalue_int_unsigned.
      apply IP.from_Z_to_Z in Heqo.
      rewrite <- IP.to_Z_to_unsigned.
      rewrite <- IS1.LP.IP.to_Z_to_unsigned.
      auto.
  Qed.

  Lemma uvalue_concretize_strict_concretize_inclusion :
    forall uv_inf uv_fin,
      uvalue_refine_strict uv_inf uv_fin ->
      uvalue_concretize_fin_inf_inclusion uv_inf uv_fin.
  Proof.
    induction uv_inf using DV1.uvalue_strong_ind;
      intros uv_fin REF;
      try solve
        [ red; intros dv_fin CONC_FIN;
          red in REF;
          cbn in REF; inv REF;

          rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN;
          red in CONC_FIN;
          rewrite CONCBASE.concretize_uvalueM_equation in CONC_FIN;
          cbn in CONC_FIN; inv CONC_FIN;

          rewrite IS1.MEM.CP.CONC.concretize_equation;
          red;
          rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation;
          cbn;
          unfold fin_to_inf_dvalue;
          break_match_goal; clear Heqs; destruct p; clear e0;
            cbn in e; inv e;
          reflexivity
        ].
    - (* Addresses *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite CONCBASE.concretize_uvalueM_equation in CONC_FIN.
      cbn in CONC_FIN; inv CONC_FIN.

      rewrite IS1.MEM.CP.CONC.concretize_equation.
      red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.
      cbn.
      unfold fin_to_inf_dvalue.
      break_match_goal.
      clear Heqs; destruct p; clear e0.
      cbn in e.
      break_match_hyp_inv.
      pose proof (addr_convert_safe _ _ Heqo0).
      pose proof (AC1.addr_convert_injective _ _ _ Heqo H); subst.
      reflexivity.
    - (* IPTR *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.

      rewrite IS1.MEM.CP.CONC.concretize_equation.
      red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.
      cbn.
      unfold fin_to_inf_dvalue.
      break_match_goal.
      clear Heqs; destruct p; clear e0.
      cbn in CONC_FIN.
      inv CONC_FIN.
      cbn in e.
      break_match_hyp_inv.
      pose proof (intptr_convert_safe _ _ Heqo0).
      pose proof IP.from_Z_injective _ _ _ Heqo H.
      apply IS1.LP.IP.to_Z_inj in H0; subst.
      reflexivity.
    - (* Undef *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF; inv REF.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite CONCBASE.concretize_uvalueM_equation in CONC_FIN.
      cbn in CONC_FIN.

      rewrite IS1.MEM.CP.CONC.concretize_equation.
      red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.
      cbn.

      destruct CONC_FIN.
      split.
      eapply dvalue_has_dtyp_fin_to_inf_dvalue; eauto.
      eapply fin_to_inf_dvalue_not_poison; auto.
    - (* Subterms *)
      { destruct uv_inf;
          try solve
            [ red; intros dv_fin CONC_FIN;
              red in REF;
              cbn in REF; inv REF;

              rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN;
              red in CONC_FIN;
              rewrite CONCBASE.concretize_uvalueM_equation in CONC_FIN;
              cbn in CONC_FIN; inv CONC_FIN;

              rewrite IS1.MEM.CP.CONC.concretize_equation;
              red;
              rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation;
              cbn;
              unfold fin_to_inf_dvalue;
              break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e;
              reflexivity
            ].

        21: {
          cbn in *.
          rename uvs into uv_bytes_inf.
          unfold uvalue_concretize_fin_inf_inclusion in *.
          intros dv_fin H0.

          red in REF.
          cbn in REF.
          break_match_hyp_inv.
          rename l into uv_bytes_fin.

          Opaque Datatypes.length N.eqb.

          rewrite IS1.MEM.CP.CONC.concretize_equation;
            red; rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation;
            cbn; repeat red.

          rewrite IS2.MEM.CP.CONC.concretize_equation in H0;
            red in H0; rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in H0;
            cbn in H0; repeat red in H0.

          replace (Datatypes.length uv_bytes_inf) with (Datatypes.length uv_bytes_fin).
          2: {
            clear - Heqo.
            symmetry.
            eapply map_monad_oom_length; eauto.
          }
          rewrite sizeof_dtyp_fin_inf.

          break_match_hyp.
          2: {
            (* Size mismatch *)
            repeat red in H0.
            destruct H0 as (?&?&?&?&?).
            destruct_err_ub_oom x; inv H1.
            destruct H2 as [[] | H2].
            specialize (H2 x1).
            forward H2; [cbn; auto|].
            remember (x0 x1) as x0x1.
            destruct_err_ub_oom x0x1; inv H4.

            eapply concretize_uvalue_bytes_helper_fin_inf in H0; eauto.
            3: eapply map_monad_oom_Forall2; eauto.

            exists (ret (fin_to_inf_dvalue_bytes x1)).
            exists (fun _ => ret (fin_to_inf_dvalue dv_fin)).
            split; eauto.
            split; eauto.
            right.
            intros a RETa.
            inv RETa.
            eapply dvalue_bytes_to_dvalue_fin_inf; eauto.
            apply dvalue_bytes_refine_fin_to_inf_dvalue_bytes.

            intros u H1 uv_fin H3 dv_fin0 H4.
            eapply H; eauto.
            eapply DVCrev.DV2.uvalue_concat_bytes_strict_subterm; eauto.

            apply concretization_map_refine_empty.
          }

          (* all_extract_bytes_from_uvalue should agree... *)
          pose proof all_extract_bytes_from_uvalue_fin_inf uv_bytes_inf uv_bytes_fin dt Heqo.
          rewrite H1.
          break_match_hyp; cbn.
          { (* This isn't structurally recursive...
           Cannot use the induction principle H to solve this goal...

           - u is the finite uvalue we get after combining all of the uvalue bytes...
           - dv_fin is the result of concretizing that uvalue...


           That said... If all bytes are from the same uvalue...
           They should be ExtractByte values that are in
           uv_bytes_inf... And `u` should be the uvalue contained in
           that ExtractByte structure... So it should be structurally
           recursive, actually?

           Nope. Failure. ExtractByte values aren't
           concretized... Could probably change this in
           concretize_uvalueM to make the induction work better, or I
           might be able to change the induction principle a bit.
             *)

            pose proof all_extract_bytes_from_uvalue_success_inv _ _ _ Heqo0 as (?&?&?).
            subst.
            cbn in H1.
            pose proof IS1.MEM.ByteM.all_extract_bytes_from_uvalue_success_inv _ _ _ H1 as (?&?&?).
            subst.
            eapply H; eauto.
            2: apply convert_fin_to_inf_uvalue_succeeds.

            pose proof Heqo0 as SUB.
            apply all_extract_bytes_from_uvalue_strict_subterm in SUB.

            eapply uvalue_strict_subterm_fin_inf.
            apply convert_fin_to_inf_uvalue_succeeds.
            repeat red.
            cbn.
            cbn in Heqo.
            rewrite Heqo.
            reflexivity.
            auto.
          }

          repeat red in H0.
          destruct H0 as (?&?&?&?&?).
          destruct_err_ub_oom x; inv H2.
          destruct H3 as [[] | H3].
          specialize (H3 x1).
          forward H3; [cbn; auto|].
          remember (x0 x1) as x0x1.
          destruct_err_ub_oom x0x1; inv H5.

          eapply concretize_uvalue_bytes_helper_fin_inf in H0; eauto.
          3: eapply map_monad_oom_Forall2; eauto.
          3: apply concretization_map_refine_empty.

          exists (ret (fin_to_inf_dvalue_bytes x1)).
          exists (fun _ => ret (fin_to_inf_dvalue dv_fin)).
          split; eauto.
          split; eauto.
          right.
          intros a RETa.
          inv RETa.
          eapply dvalue_bytes_to_dvalue_fin_inf; eauto.
          apply dvalue_bytes_refine_fin_to_inf_dvalue_bytes.

          intros * ? ? ? ? ?.
          eapply H; eauto.
          eapply DVCrev.DV2.uvalue_concat_bytes_strict_subterm; eauto.
        }

        - (* Addresses *)
          red; intros dv_fin CONC_FIN.
          red in REF.
          cbn in REF.
          break_match_hyp_inv.
          rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
          red in CONC_FIN.
          rewrite CONCBASE.concretize_uvalueM_equation in CONC_FIN.
          cbn in CONC_FIN; inv CONC_FIN.

          rewrite IS1.MEM.CP.CONC.concretize_equation.
          red.
          rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.
          cbn.
          unfold fin_to_inf_dvalue.
          break_match_goal.
          clear Heqs; destruct p; clear e0.
          cbn in e.
          break_match_hyp_inv.
          pose proof (addr_convert_safe _ _ Heqo0).
          pose proof (AC1.addr_convert_injective _ _ _ Heqo H0); subst.
          reflexivity.
        - (* IPTR *)
          red; intros dv_fin CONC_FIN.
          red in REF.
          cbn in REF.
          break_match_hyp_inv.

          rewrite IS1.MEM.CP.CONC.concretize_equation.
          red.
          rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.
          cbn.
          unfold fin_to_inf_dvalue.
          break_match_goal.
          clear Heqs; destruct p; clear e0.
          cbn in CONC_FIN.
          inv CONC_FIN.
          cbn in e.
          break_match_hyp_inv.
          pose proof (intptr_convert_safe _ _ Heqo0).
          pose proof IP.from_Z_injective _ _ _ Heqo H0.
          apply IS1.LP.IP.to_Z_inj in H1; subst.
          reflexivity.
        - (* Undef *)
          red; intros dv_fin CONC_FIN.
          red in REF.
          cbn in REF; inv REF.

          rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
          red in CONC_FIN.
          rewrite CONCBASE.concretize_uvalueM_equation in CONC_FIN.
          cbn in CONC_FIN.

          rewrite IS1.MEM.CP.CONC.concretize_equation.
          red.
          rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.
          cbn.

          destruct CONC_FIN.
          split.
          eapply dvalue_has_dtyp_fin_to_inf_dvalue; eauto.
          eapply fin_to_inf_dvalue_not_poison; auto.
        - (* Struct *)
          red; intros dv_fin CONC_FIN.
          red in REF.
          cbn in REF.
          break_match_hyp_inv.

          unfold uvalue_concretize_fin_inf_inclusion in H.
          apply map_monad_oom_Forall2 in Heqo.

          rewrite IS1.MEM.CP.CONC.concretize_equation.
          red.
          rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

          rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
          red in CONC_FIN.
          rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.

          repeat red in CONC_FIN.
          destruct CONC_FIN as (?&?&?&?&?).
          destruct_err_ub_oom x; cbn in H1; inv H1.
          destruct H2 as [[] | H2].
          specialize (H2 x1 eq_refl).
          cbn in H2.
          rewrite <- H2 in H4.
          cbn in H4. inv H4.

          rename H0 into MAP.

          repeat red.
          exists (ret (map fin_to_inf_dvalue x1)).
          exists (fun fields => ret (IS1.LP.Events.DV.DVALUE_Struct fields)).
          split.
          { eapply map_monad_ErrUbOomProp_forall2.
            apply Util.Forall2_forall.
            split.
            - rewrite length_map.

              apply map_monad_ErrUbOomProp_length in MAP.
              apply Util.Forall2_length in Heqo.
              congruence.
            - intros i a b NTH_fields NTH_res.

              epose proof Util.Forall2_Nth_left NTH_fields Heqo as (x&NTHl&CONV).

              apply Util.Nth_In in NTH_fields.
              specialize (H a).
              forward H; [constructor; constructor; auto|].
              specialize (H x CONV).

              eapply map_monad_ErrUbOomProp_forall2 in MAP.
              epose proof Util.Forall2_Nth_left NTHl MAP as (?&NTH_CONC&CONC).
              specialize (H _ CONC).

              apply Nth_map_iff in NTH_res as (?&?&?).
              subst.

              red in NTH_CONC, H1.
              rewrite H1 in NTH_CONC.
              inv NTH_CONC.
              apply H.
          }

          cbn.
          split.
          { unfold fin_to_inf_dvalue at 2.
            break_match_goal.
            clear Heqs; destruct p; clear e0.

            erewrite <- dvalue_convert_strict_struct_map; eauto.
          }

          right.
          intros a H0.
          reflexivity.
    - (* Packed structs *)
          red; intros dv_fin CONC_FIN.
          red in REF.
          cbn in REF.
          break_match_hyp_inv.

          unfold uvalue_concretize_fin_inf_inclusion in H.
          apply map_monad_oom_Forall2 in Heqo.

          rewrite IS1.MEM.CP.CONC.concretize_equation.
          red.
          rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

          rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
          red in CONC_FIN.
          rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.

          repeat red in CONC_FIN.
          destruct CONC_FIN as (?&?&?&?&?).
          destruct_err_ub_oom x; cbn in H1; inv H1.
          destruct H2 as [[] | H2].
          specialize (H2 x1 eq_refl).
          cbn in H2.
          rewrite <- H2 in H4.
          cbn in H4. inv H4.

          rename H0 into MAP.

          repeat red.
          exists (ret (map fin_to_inf_dvalue x1)).
          exists (fun fields => ret (IS1.LP.Events.DV.DVALUE_Packed_struct fields)).
          split.
          { eapply map_monad_ErrUbOomProp_forall2.
            apply Util.Forall2_forall.
            split.
            - rewrite length_map.

              apply map_monad_ErrUbOomProp_length in MAP.
              apply Util.Forall2_length in Heqo.
              congruence.
            - intros i a b NTH_fields NTH_res.

              epose proof Util.Forall2_Nth_left NTH_fields Heqo as (x&NTHl&CONV).

              apply Util.Nth_In in NTH_fields.
              specialize (H a).
              forward H; [constructor; constructor; auto|].
              specialize (H x CONV).

              eapply map_monad_ErrUbOomProp_forall2 in MAP.
              epose proof Util.Forall2_Nth_left NTHl MAP as (?&NTH_CONC&CONC).
              specialize (H _ CONC).

              apply Nth_map_iff in NTH_res as (?&?&?).
              subst.

              red in NTH_CONC, H1.
              rewrite H1 in NTH_CONC.
              inv NTH_CONC.
              apply H.
          }

          cbn.
          split.
          { unfold fin_to_inf_dvalue at 2.
            break_match_goal.
            clear Heqs; destruct p; clear e0.

            erewrite <- dvalue_convert_strict_packed_struct_map; eauto.
          }

          right.
          intros a H0.
          reflexivity.
    - (* Array *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.

      unfold uvalue_concretize_fin_inf_inclusion in H.
      apply map_monad_oom_Forall2 in Heqo.

      rewrite IS1.MEM.CP.CONC.concretize_equation.
      red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.

      repeat red in CONC_FIN.
      destruct CONC_FIN as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; inv H1.
      destruct H2 as [[] | H2].
      specialize (H2 x1 eq_refl).
      cbn in H2.
      rewrite <- H2 in H4.
      cbn in H4. inv H4.

      rename H0 into MAP.

      repeat red.
      exists (ret (map fin_to_inf_dvalue x1)).
      exists (fun fields => ret (IS1.LP.Events.DV.DVALUE_Array t fields)).
      split.
      { eapply map_monad_ErrUbOomProp_forall2.
        apply Util.Forall2_forall.
        split.
        - rewrite length_map.

          apply map_monad_ErrUbOomProp_length in MAP.
          apply Util.Forall2_length in Heqo.
          congruence.
        - intros i a b NTH_fields NTH_res.

          epose proof Util.Forall2_Nth_left NTH_fields Heqo as (x&NTHl&CONV).

          apply Util.Nth_In in NTH_fields.
          specialize (H a).
          forward H; [constructor; constructor; auto|].
          specialize (H x CONV).

          eapply map_monad_ErrUbOomProp_forall2 in MAP.
          epose proof Util.Forall2_Nth_left NTHl MAP as (?&NTH_CONC&CONC).
          specialize (H _ CONC).

          apply Nth_map_iff in NTH_res as (?&?&?).
          subst.

          red in NTH_CONC, H1.
          rewrite H1 in NTH_CONC.
          inv NTH_CONC.
          apply H.
      }

      cbn.
      split.
      { unfold fin_to_inf_dvalue at 2.
        break_match_goal.
        clear Heqs; destruct p; clear e0.

        erewrite <- dvalue_convert_strict_array_map; eauto.
      }

      right.
      intros a H0.
      reflexivity.
    - (* Vector *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.

      unfold uvalue_concretize_fin_inf_inclusion in H.
      apply map_monad_oom_Forall2 in Heqo.

      rewrite IS1.MEM.CP.CONC.concretize_equation.
      red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.

      repeat red in CONC_FIN.
      destruct CONC_FIN as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; inv H1.
      destruct H2 as [[] | H2].
      specialize (H2 x1 eq_refl).
      cbn in H2.
      rewrite <- H2 in H4.
      cbn in H4. inv H4.

      rename H0 into MAP.

      repeat red.
      exists (ret (map fin_to_inf_dvalue x1)).
      exists (fun fields => ret (IS1.LP.Events.DV.DVALUE_Vector t fields)).
      split.
      { eapply map_monad_ErrUbOomProp_forall2.
        apply Util.Forall2_forall.
        split.
        - rewrite length_map.

          apply map_monad_ErrUbOomProp_length in MAP.
          apply Util.Forall2_length in Heqo.
          congruence.
        - intros i a b NTH_fields NTH_res.

          epose proof Util.Forall2_Nth_left NTH_fields Heqo as (x&NTHl&CONV).

          apply Util.Nth_In in NTH_fields.
          specialize (H a).
          forward H; [constructor; constructor; auto|].
          specialize (H x CONV).

          eapply map_monad_ErrUbOomProp_forall2 in MAP.
          epose proof Util.Forall2_Nth_left NTHl MAP as (?&NTH_CONC&CONC).
          specialize (H _ CONC).

          apply Nth_map_iff in NTH_res as (?&?&?).
          subst.

          red in NTH_CONC, H1.
          rewrite H1 in NTH_CONC.
          inv NTH_CONC.
          apply H.
      }

      cbn.
      split.
      { unfold fin_to_inf_dvalue at 2.
        break_match_goal.
        clear Heqs; destruct p; clear e0.

        erewrite <- dvalue_convert_strict_vector_map; eauto.
      }

      right.
      intros a H0.
      reflexivity.
    - (* IBinop *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      break_match_hyp_inv.

      unfold uvalue_concretize_fin_inf_inclusion in H.

      pose proof (H uv_inf1) as IHuv_inf1.
      forward IHuv_inf1; [constructor; constructor; auto|].

      pose proof (H uv_inf2) as IHuv_inf2.
      forward IHuv_inf2; [constructor; constructor; auto|].

      specialize (IHuv_inf1 u Heqo).
      specialize (IHuv_inf2 u0 Heqo0).

      rewrite IS1.MEM.CP.CONC.concretize_equation.
      red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.

      repeat red in CONC_FIN.
      destruct CONC_FIN as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; inv H1.
      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).
      cbn in H2.
      repeat red in H2.
      destruct H2 as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H2; rewrite <- H2 in H4; inv H4.
      destruct H3 as [[] | H3].
      specialize (H3 _ eq_refl).
      rewrite <- H3 in H6, H2.

      remember (eval_iop iop x1 x3) as x1x3.
      destruct_err_ub_oom x1x3; inv H6.
      cbn in H2.

      apply IHuv_inf1 in H0.
      apply IHuv_inf2 in H1.

      repeat red.
      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))).
      cbn.
      rewrite <- H2.
      cbn.
      split; eauto.
      split; eauto.

      right.
      intros a H4.
      repeat red.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 x3))).
      cbn.
      rewrite <- H3.
      cbn.
      split; eauto.
      split; eauto.

      right.
      intros a0 H5.

      eapply eval_iop_fin_inf; eauto.
    - (* ICmp *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      break_match_hyp_inv.

      unfold uvalue_concretize_fin_inf_inclusion in H.

      pose proof (H uv_inf1) as IHuv_inf1.
      forward IHuv_inf1; [constructor; constructor; auto|].

      pose proof (H uv_inf2) as IHuv_inf2.
      forward IHuv_inf2; [constructor; constructor; auto|].

      specialize (IHuv_inf1 u Heqo).
      specialize (IHuv_inf2 u0 Heqo0).

      rewrite IS1.MEM.CP.CONC.concretize_equation.
      red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.

      repeat red in CONC_FIN.
      destruct CONC_FIN as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; inv H1.
      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).
      cbn in H2.
      repeat red in H2.
      destruct H2 as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H2; rewrite <- H2 in H4; inv H4.
      destruct H3 as [[] | H3].
      specialize (H3 _ eq_refl).
      rewrite <- H3 in H6, H2.

      remember (eval_icmp cmp x1 x3) as x1x3.
      destruct_err_ub_oom x1x3; inv H6.
      cbn in H2.

      apply IHuv_inf1 in H0.
      apply IHuv_inf2 in H1.

      repeat red.
      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))).
      cbn.
      rewrite <- H2.
      cbn.
      split; eauto.
      split; eauto.

      right.
      intros a H4.
      repeat red.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 x3))).
      cbn.
      rewrite <- H3.
      cbn.
      split; eauto.
      split; eauto.

      right.
      intros a0 H5.

      eapply eval_icmp_fin_inf; eauto.
    - (* FBinop *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      break_match_hyp_inv.

      unfold uvalue_concretize_fin_inf_inclusion in H.

      pose proof (H uv_inf1) as IHuv_inf1.
      forward IHuv_inf1; [constructor; constructor; auto|].

      pose proof (H uv_inf2) as IHuv_inf2.
      forward IHuv_inf2; [constructor; constructor; auto|].

      specialize (IHuv_inf1 u Heqo).
      specialize (IHuv_inf2 u0 Heqo0).

      rewrite IS1.MEM.CP.CONC.concretize_equation.
      red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.

      repeat red in CONC_FIN.
      destruct CONC_FIN as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; inv H1.
      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).
      cbn in H2.
      repeat red in H2.
      destruct H2 as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H2; rewrite <- H2 in H4; inv H4.
      destruct H3 as [[] | H3].
      specialize (H3 _ eq_refl).
      rewrite <- H3 in H6, H2.

      remember (eval_fop fop x1 x3) as x1x3.
      destruct_err_ub_oom x1x3; inv H6.
      cbn in H2.

      apply IHuv_inf1 in H0.
      apply IHuv_inf2 in H1.

      repeat red.
      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))).
      cbn.
      rewrite <- H2.
      cbn.
      split; eauto.
      split; eauto.

      right.
      intros a H4.
      repeat red.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 x3))).
      cbn.
      rewrite <- H3.
      cbn.
      split; eauto.
      split; eauto.

      right.
      intros a0 H5.

      eapply eval_fop_fin_inf; eauto.
    - (* fcmp *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      break_match_hyp_inv.

      unfold uvalue_concretize_fin_inf_inclusion in H.

      pose proof (H uv_inf1) as IHuv_inf1.
      forward IHuv_inf1; [constructor; constructor; auto|].

      pose proof (H uv_inf2) as IHuv_inf2.
      forward IHuv_inf2; [constructor; constructor; auto|].

      specialize (IHuv_inf1 u Heqo).
      specialize (IHuv_inf2 u0 Heqo0).

      rewrite IS1.MEM.CP.CONC.concretize_equation.
      red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.

      repeat red in CONC_FIN.
      destruct CONC_FIN as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; inv H1.
      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).
      cbn in H2.
      repeat red in H2.
      destruct H2 as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H2; rewrite <- H2 in H4; inv H4.
      destruct H3 as [[] | H3].
      specialize (H3 _ eq_refl).
      rewrite <- H3 in H6, H2.

      remember (eval_fcmp cmp x1 x3) as x1x3.
      destruct_err_ub_oom x1x3; inv H6.
      cbn in H2.

      apply IHuv_inf1 in H0.
      apply IHuv_inf2 in H1.

      repeat red.
      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))).
      cbn.
      rewrite <- H2.
      cbn.
      split; eauto.
      split; eauto.

      right.
      intros a H4.
      repeat red.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 x3))).
      cbn.
      rewrite <- H3.
      cbn.
      split; eauto.
      split; eauto.

      right.
      intros a0 H5.

      eapply eval_fcmp_fin_inf; eauto.
    - (* Conversion *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.

      rename H into IH.
      pose proof (IH uv_inf) as IHuv_inf.
      forward IHuv_inf; [constructor; constructor; auto|].

      specialize (IHuv_inf _ Heqo).
      unfold uvalue_concretize_fin_inf_inclusion in IHuv_inf.

      rewrite IS1.MEM.CP.CONC.concretize_equation.
      red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.

      repeat red in CONC_FIN.
      destruct CONC_FIN as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H0; inv H0.
      destruct H1 as [[] | H1].
      specialize (H1 _ eq_refl).
      cbn in H1.

      specialize (IHuv_inf _ H).
      repeat red.
      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => (fmap fin_to_inf_dvalue (x0 x1))).
      cbn; rewrite H3; cbn.
      split; eauto.
      split; eauto.

      right; intros ? ?; subst.
      break_match_hyp.
      { (* Conv_Pure *)
        pose proof get_conv_case_pure_fin_inf _ _ _ _ _ Heqc as CONV.
        rewrite CONV.
        remember (x0 x1) as x0x1.
        destruct_err_ub_oom x0x1; inv H3.
        inv H1; auto.
      }

      { (* Conv_ItoP *)
        break_match_hyp;
          rewrite <- H1 in H3; inv H3.

        pose proof get_conv_case_itop_fin_inf _ _ _ _ _ Heqc as CONV.
        rewrite CONV.
        cbn.

        erewrite dvalue_int_unsigned_E1E2;
          [|apply fin_to_inf_dvalue_refine_strict].

        erewrite int_to_ptr_fin_inf_wildcard; eauto.
        rewrite_fin_to_inf_dvalue; reflexivity.

        unfold fin_to_inf_addr.
        break_match_goal; clear Heqs; auto.
      }

      { (* Conv_PtoI *)
        remember (x0 x1) as x0x1.
        destruct_err_ub_oom x0x1; inv H3.
        break_match_hyp; try inv H1.
        pose proof get_conv_case_ptoi_fin_inf _ _ _ _ _ Heqc as CONV.
        break_match_hyp_inv.
        { repeat break_match_hyp_inv;
            rewrite CONV; rewrite_fin_to_inf_dvalue;
            rewrite ptr_to_int_fin_to_inf_addr; auto.
        }

        remember (lift_OOM (mrepr (PTOI.ptr_to_int a))) as ptoi.
        destruct_err_ub_oom ptoi; cbn in H2; inv H2.
        rewrite CONV; rewrite_fin_to_inf_dvalue.
        erewrite ptr_to_int_fin_to_inf_addr; eauto.
        destruct (mrepr (PTOI.ptr_to_int a)) eqn:HREPR; inv Heqptoi.
        erewrite VMEM_REF.mrepr_refine with (x_inf:=(intptr_fin_inf i)).
        3: apply HREPR.
        2: {
          unfold intptr_fin_inf.
          break_match_goal.
          clear Heqs.
          eapply intptr_convert_safe in e.
          erewrite IP.from_Z_to_Z; eauto.
        }
        cbn.
        reflexivity.
      }

      { (* Conv_Oom *)
        exfalso.
        rewrite <- H1 in H3; inv H3.
      }

      { (* Conv_Illegal *)
        exfalso.
        rewrite <- H1 in H3; inv H3.
      }
    - (* GetElementPtr *)
      rename H into IH.
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      break_match_hyp_inv.

      pose proof (IH uv_inf) as IHuv_inf.
      forward IHuv_inf; [constructor; constructor; auto|].

      pose proof (IHuv_inf u Heqo) as IHuv_inf_u.
      unfold uvalue_concretize_fin_inf_inclusion in IHuv_inf_u.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.

      repeat red in CONC_FIN.
      destruct CONC_FIN as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H0; inv H0.
      destruct H1 as [[] | H1].
      specialize (H1 _ eq_refl).
      cbn in H1.
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; rewrite <- H1 in H3; inv H3.
      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).
      break_match_hyp; try rewrite <- H2 in H5; inv H5.
      break_match_hyp; try rewrite <- H2 in H4; inv H4.
      rewrite <- H2 in H1; cbn in H1.

      specialize (IHuv_inf_u _ H).
      destruct x1; cbn in Heqs; inv Heqs.
      break_match_hyp_inv.
      break_match_hyp_inv.

      pose proof addr_convert_succeeds a as (a'&AA').
      pose proof addr_convert_succeeds a0 as (a0'&A0A0').
      epose proof (handle_gep_addr_fin_inf _ _ _ _ _ _ _ Heqs AA' A0A0' eq_refl).

      rewrite IS1.MEM.CP.CONC.concretize_equation.
      red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red.
      exists (ret (fin_to_inf_dvalue (DVALUE_Addr a))).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 (DVALUE_Addr a)))).
      rewrite <- H1.
      split; eauto.
      split; cbn; eauto.

      right.
      intros a1 ?; subst.
      repeat red.
      exists (ret (fmap fin_to_inf_dvalue x3)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 x3))).
      cbn.
      split; eauto.
      { clear - IH H0 Heqo0.
        rename IH into H.
        apply map_monad_oom_Forall2 in Heqo0.
        generalize dependent x3.
        induction Heqo0; intros x3 H1.
        - cbn in *; inv H1; cbn; auto.
        - forward IHHeqo0.
          { intros idx H2 uv_fin H3.
            eapply H; eauto.
            eapply DV1.uvalue_strict_subterm_inv in H2
                as (?&?&?).
            inv H2.
            - eapply clos_rt_t; [apply H4|].
              constructor; constructor; auto.
            - eapply clos_rt_t; [apply H4|].
              constructor.
              eapply DV1.UVALUE_GetElementPtr_subterm_idxs.
              right; auto.
          }

          rewrite map_monad_unfold in H1.
          repeat red in H1.
          destruct H1 as (?&?&?&?&?).
          destruct_err_ub_oom x0; inv H2.
          destruct H3 as [[] | H3].
          specialize (H3 _ eq_refl).

          repeat red in H3.
          destruct H3 as (?&?&?&?&?).
          rewrite <- H3 in H5.
          destruct_err_ub_oom x0; inv H5.

          destruct H4 as [[] | H4].
          specialize (H4 _ eq_refl).
          cbn in H4.

          rewrite <- H4 in H7; inv H7.
          cbn in H3; rewrite <- H4 in H3; inv H3.

          specialize (IHHeqo0 _ H2).
          rewrite map_monad_unfold.
          repeat red.

          pose proof (H x).
          forward H3.
          constructor.
          eapply DV1.UVALUE_GetElementPtr_subterm_idxs; left; eauto.
          specialize (H3 _ H0 _ H1).

          exists (ret (fin_to_inf_dvalue x2)).
          exists (fun dv_inf => fmap (fmap fin_to_inf_dvalue) (x1 x2)).

          cbn; rewrite <- H6; cbn.
          split; eauto.
          split; eauto.

          right.
          intros a ?; subst.
          repeat red.
          exists (ret (fmap fin_to_inf_dvalue x5)).
          exists (fun dv_inf => (fmap (fmap fin_to_inf_dvalue) (x4 x5))).

          cbn; rewrite <- H4; cbn.
          split; eauto.
          split; eauto.

          right.
          intros a ?; subst.
          auto.
      }

      cbn; rewrite <- H2; cbn.
      split; eauto.

      right.
      intros a1 ?; subst.
      unfold fin_to_inf_dvalue at 1.
      break_inner_match_goal; clear Heqs0; destruct p; clear e0.
      cbn in e.
      rewrite AA' in e.
      inv e.
      cbn.

      replace (map fin_to_inf_dvalue x3) with (fmap fin_to_inf_dvalue x3) in H3 by reflexivity.
      cbn in H3.
      rewrite H3.

      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs0; destruct p; clear e0.
      cbn in e.
      rewrite A0A0' in e.
      inv e.
      reflexivity.
    - (* ExtractElement *)
      rename H into IH.
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      break_match_hyp_inv.

      pose proof (IH uv_inf1) as IHuv_inf1.
      forward IHuv_inf1; [constructor; constructor; auto|].

      pose proof (IH uv_inf2) as IHuv_inf2.
      forward IHuv_inf2; [constructor; constructor; auto|].

      pose proof (IHuv_inf1 u Heqo) as IHuv_inf_u.
      pose proof (IHuv_inf2 u0 Heqo0) as IHuv_inf_u0.

      unfold uvalue_concretize_fin_inf_inclusion in IHuv_inf_u, IHuv_inf_u0.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.

      repeat red in CONC_FIN.
      destruct CONC_FIN as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      destruct H1 as [[] | H1].
      specialize (H1 _ eq_refl).
      cbn in H1.
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; rewrite <- H1 in H3; inv H3.
      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).

      repeat red in H2.
      destruct H2 as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H3; rewrite <- H3 in H5; inv H5.
      destruct H4 as [[] | H4].
      specialize (H4 _ eq_refl).

      remember (x4 x5) as x4x5.
      destruct_err_ub_oom x4x5; inv H7.
      cbn in H3.
      rewrite <- H3 in H1.
      cbn in H1.

      break_match_hyp_inv.

      specialize (IHuv_inf_u _ H).
      specialize (IHuv_inf_u0 _ H0).

      rewrite IS1.MEM.CP.CONC.concretize_equation.
      red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red.
      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))).
      cbn.
      rewrite <- H1.
      cbn.
      split; eauto.
      split; eauto.

      right.
      intros a ?; subst.
      repeat red.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 x3))).
      cbn; rewrite <- H3; cbn.
      split; eauto.
      split; eauto.

      right.
      intros a ?; subst.
      repeat red.
      exists (ret x5).
      exists (fun x5 => fmap fin_to_inf_dvalue (x4 x5)).
      cbn; rewrite <- Heqx4x5; cbn.
      split; eauto.
      split; eauto.

      right.
      intros a ?; subst.
      cbn; rewrite <- Heqx4x5; cbn.

      eapply index_into_vec_dv_fin_inf; eauto.
    - (* InsertElement *)
      rename H into IH.
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      break_match_hyp_inv.
      break_match_hyp_inv.

      pose proof (IH uv_inf1) as IHuv_inf1.
      forward IHuv_inf1; [constructor; constructor; auto|].

      pose proof (IH uv_inf2) as IHuv_inf2.
      forward IHuv_inf2; [constructor; constructor; auto|].

      pose proof (IH uv_inf3) as IHuv_inf3.
      forward IHuv_inf3; [constructor; constructor; auto|].

      pose proof (IHuv_inf1 u Heqo) as IHuv_inf_u.
      pose proof (IHuv_inf2 u0 Heqo0) as IHuv_inf_u0.
      pose proof (IHuv_inf3 u1 Heqo1) as IHuv_inf_u1.

      unfold uvalue_concretize_fin_inf_inclusion in IHuv_inf_u, IHuv_inf_u0, IHuv_inf_u1.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.

      repeat red in CONC_FIN.
      destruct CONC_FIN as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      destruct H1 as [[] | H1].
      specialize (H1 _ eq_refl).
      cbn in H1.

      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; rewrite <- H1 in H3; inv H3.
      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).

      repeat red in H2.
      destruct H2 as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H3; rewrite <- H3 in H5; inv H5.
      destruct H4 as [[] | H4].
      specialize (H4 _ eq_refl).

      remember (x4 x5) as x4x5.
      destruct_err_ub_oom x4x5; inv H7.
      cbn in H3.
      rewrite <- H3 in H1.
      cbn in H1.

      specialize (IHuv_inf_u _ H).
      specialize (IHuv_inf_u0 _ H2).
      specialize (IHuv_inf_u1 _ H0).

      rewrite IS1.MEM.CP.CONC.concretize_equation.
      red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red.
      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))).
      cbn.
      rewrite <- H1.
      cbn.
      split; eauto.
      split; eauto.

      right.
      intros a ?; subst.
      repeat red.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 x3))).
      cbn; rewrite <- H3; cbn.
      split; eauto.
      split; eauto.

      right.
      intros a ?; subst.
      repeat red.
      exists (ret (fin_to_inf_dvalue x5)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x4 x5))).
      cbn; rewrite <- Heqx4x5; cbn.
      split; eauto.
      split; eauto.

      right.
      intros a ?; subst.

      eapply insert_into_vec_dv_fin_inf; eauto.
    - (* ShuffleVector *)
      rename H into IH.
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      break_match_hyp_inv.
      break_match_hyp_inv.

      pose proof (IH uv_inf1) as IHuv_inf1.
      forward IHuv_inf1; [constructor; constructor; auto|].

      pose proof (IH uv_inf2) as IHuv_inf2.
      forward IHuv_inf2; [constructor; constructor; auto|].

      pose proof (IH uv_inf3) as IHuv_inf3.
      forward IHuv_inf3; [constructor; constructor; auto|].

      pose proof (IHuv_inf1 u Heqo) as IHuv_inf_u.
      pose proof (IHuv_inf2 u0 Heqo0) as IHuv_inf_u0.
      pose proof (IHuv_inf3 u1 Heqo1) as IHuv_inf_u1.

      unfold uvalue_concretize_fin_inf_inclusion in IHuv_inf_u, IHuv_inf_u0, IHuv_inf_u1.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.
      inv CONC_FIN.
    - (* ExtractValue *)
      rename H into IH.
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.
      cbn in CONC_FIN.
      repeat red in CONC_FIN.

      destruct CONC_FIN as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      destruct H1 as [[] | H1].
      specialize (H1 _ eq_refl).

      remember (x0 x1) as x0x1.
      destruct_err_ub_oom x0x1; inv H3.
      apply extract_value_loop_fin_inf_succeeds in H1.

      rewrite IS1.MEM.CP.CONC.concretize_equation;
        red; rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation;
        cbn; repeat red.

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))).
      cbn; rewrite <- Heqx0x1; cbn.
      split.
      eapply IH; eauto.
      constructor; constructor; auto.
      split; eauto.

      right.
      intros a ?; subst.
      auto.
    - (* InsertValue *)
      rename H into IH.
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      break_match_hyp_inv.

      pose proof (IH uv_inf1) as IHuv_inf1.
      forward IHuv_inf1; [constructor; constructor; auto|].

      pose proof (IH uv_inf2) as IHuv_inf2.
      forward IHuv_inf2; [constructor; constructor; auto|].

      pose proof (IHuv_inf1 u Heqo) as IHuv_inf_u.
      pose proof (IHuv_inf2 u0 Heqo0) as IHuv_inf_u0.
      red in IHuv_inf_u, IHuv_inf_u0.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.
      cbn in CONC_FIN.

      repeat red in CONC_FIN.
      destruct CONC_FIN as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      destruct H1 as [[] | H1].
      specialize (H1 _ eq_refl).

      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.
      cbn in H1.
      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).

      specialize (IHuv_inf_u _ H).
      specialize (IHuv_inf_u0 _ H0).

      rewrite IS1.MEM.CP.CONC.concretize_equation;
        red; rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation;
        cbn; repeat red.

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))).
      cbn; rewrite <- H1, H5; cbn.
      split; eauto.
      split; eauto.

      right.
      intros a ?; subst.
      repeat red.

      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 x3))).
      cbn; rewrite H5; cbn.
      split; eauto.
      split; eauto.

      right.
      intros a ?; subst.
      eapply insert_value_loop_fin_inf_succeeds in H2.
      setoid_rewrite H2.
      remember (x2 x3) as x2x3.
      destruct_err_ub_oom x2x3; inv H5.
      reflexivity.
    - (* Select *)
      rename H into IH.
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      break_match_hyp_inv.
      break_match_hyp_inv.

      pose proof (IH uv_inf1) as IHuv_inf1.
      forward IHuv_inf1; [constructor; constructor; auto|].

      pose proof (IH uv_inf2) as IHuv_inf2.
      forward IHuv_inf2; [constructor; constructor; auto|].

      pose proof (IH uv_inf3) as IHuv_inf3.
      forward IHuv_inf3; [constructor; constructor; auto|].

      pose proof (IHuv_inf1 u Heqo) as IHuv_inf_u.
      pose proof (IHuv_inf2 u0 Heqo0) as IHuv_inf_u0.
      pose proof (IHuv_inf3 u1 Heqo1) as IHuv_inf_u1.
      red in IHuv_inf_u, IHuv_inf_u0, IHuv_inf_u1.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.
      cbn in CONC_FIN.

      repeat red in CONC_FIN.
      destruct CONC_FIN as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      destruct H1 as [[] | H1].
      specialize (H1 _ eq_refl).

      remember (x0 x1) as x0x1.
      destruct_err_ub_oom x0x1; inv H3.
      pose proof eval_select_fin_inf x1 u0 u1 _ _ dv_fin IHuv_inf_u0 IHuv_inf_u1 as EVAL.
      forward EVAL.
      { cbn.
        rewrite eval_select_equation.
        apply H1.
      }

      rewrite IS1.MEM.CP.CONC.concretize_equation;
        red; rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation;
        cbn; repeat red.

      specialize (IHuv_inf_u _ H).

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))).
      split; eauto.
      split; cbn; rewrite <- Heqx0x1; cbn; eauto.

      right.
      intros a ?; subst.
      rewrite IS1.MEM.CP.CONC.eval_select_equation in EVAL.
      apply EVAL.
    - (* ExtractByte *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      cbn in *.
      inv CONC_FIN.
      }
  Qed.

  Lemma fin_to_inf_dvalue_injective :
    forall dv1 dv2,
      fin_to_inf_dvalue dv1 = fin_to_inf_dvalue dv2 ->
      dv1 = dv2.
  Proof.
    induction dv1;
      intros dv2 LIFT.
    - unfold fin_to_inf_dvalue in *.
      break_match_hyp; clear Heqs; destruct p; clear e0.
      break_match_hyp_inv; clear Heqs; destruct p; clear e1.
      cbn in e.
      break_match_hyp_inv.
      eapply DVCrev.dvalue_convert_strict_addr_inv in e0.
      destruct e0 as (?&?&?).
      subst.
      pose proof AC2.addr_convert_injective _ _ _ H0 Heqo; subst; auto.
    - unfold fin_to_inf_dvalue in *.
      break_match_hyp; clear Heqs; destruct p; clear e0.
      break_match_hyp_inv; clear Heqs; destruct p; clear e1.
      cbn in e.
      inv e.
      eapply DVCrev.dvalue_convert_strict_ix_inv in e0.
      subst; auto.
    - unfold fin_to_inf_dvalue in *.
      break_match_hyp; clear Heqs; destruct p; clear e0.
      break_match_hyp_inv; clear Heqs; destruct p; clear e1.
      cbn in e.
      break_match_hyp_inv.
      eapply DVCrev.dvalue_convert_strict_iptr_inv in e0.
      destruct e0 as (?&?&?); subst.
      pose proof IS1.LP.IP.from_Z_injective _ _ _ H0 Heqo.
      apply IP.to_Z_inj in H1; subst; auto.
    - unfold fin_to_inf_dvalue in *.
      break_match_hyp; clear Heqs; destruct p; clear e0.
      break_match_hyp_inv; clear Heqs; destruct p; clear e1.
      cbn in e.
      inv e.
      eapply DVCrev.dvalue_convert_strict_double_inv in e0.
      subst; auto.
    - unfold fin_to_inf_dvalue in *.
      break_match_hyp; clear Heqs; destruct p; clear e0.
      break_match_hyp_inv; clear Heqs; destruct p; clear e1.
      cbn in e.
      inv e.
      eapply DVCrev.dvalue_convert_strict_float_inv in e0.
      subst; auto.
    - unfold fin_to_inf_dvalue in *.
      break_match_hyp; clear Heqs; destruct p; clear e0.
      break_match_hyp_inv; clear Heqs; destruct p; clear e1.
      cbn in e.
      inv e.
      eapply DVCrev.dvalue_convert_strict_poison_inv in e0.
      subst; auto.
    - unfold fin_to_inf_dvalue in *.
      break_match_hyp; clear Heqs; destruct p; clear e0.
      break_match_hyp_inv; clear Heqs; destruct p; clear e1.
      cbn in e.
      inv e.
      eapply DVCrev.dvalue_convert_strict_oom_inv in e0.
      subst; auto.
    - unfold fin_to_inf_dvalue in *.
      break_match_hyp; clear Heqs; destruct p; clear e0.
      break_match_hyp_inv; clear Heqs; destruct p; clear e1.
      cbn in e.
      inv e.
      eapply DVCrev.dvalue_convert_strict_none_inv in e0.
      subst; auto.
    - unfold fin_to_inf_dvalue in LIFT.
      break_match_hyp; clear Heqs; destruct p; clear e0.
      break_match_hyp_inv; clear Heqs; destruct p; clear e1.
      cbn in e.
      break_match_hyp_inv.
      clear H0.
      eapply DVCrev.dvalue_convert_strict_struct_inv in e0.
      destruct e0 as (?&?&?).
      subst.
      eapply map_monad_oom_Forall2 in H1, Heqo.
      assert (fields=x) as FX.
      { eapply Forall2_inj_OOM_l; eauto.
        intros a H0 a' b H2 H3.
        pose proof DVCrev.dvalue_refine_strict_R2_injective _ _ _ _ H2 H3 as (_&?).
        forward H4; auto; subst.
      }
      subst.
      reflexivity.
    - unfold fin_to_inf_dvalue in LIFT.
      break_match_hyp; clear Heqs; destruct p; clear e0.
      break_match_hyp_inv; clear Heqs; destruct p; clear e1.
      cbn in e.
      break_match_hyp_inv.
      clear H0.
      eapply DVCrev.dvalue_convert_strict_packed_struct_inv in e0.
      destruct e0 as (?&?&?).
      subst.
      eapply map_monad_oom_Forall2 in H1, Heqo.
      assert (fields=x) as FX.
      { eapply Forall2_inj_OOM_l; eauto.
        intros a H0 a' b H2 H3.
        pose proof DVCrev.dvalue_refine_strict_R2_injective _ _ _ _ H2 H3 as (_&?).
        forward H4; auto; subst.
      }
      subst.
      reflexivity.
    - unfold fin_to_inf_dvalue in LIFT.
      break_match_hyp; clear Heqs; destruct p; clear e0.
      break_match_hyp_inv; clear Heqs; destruct p; clear e1.
      cbn in e.
      break_match_hyp_inv.
      clear H0.
      eapply DVCrev.dvalue_convert_strict_array_inv in e0.
      destruct e0 as (?&?&?).
      subst.
      eapply map_monad_oom_Forall2 in H1, Heqo.
      assert (elts=x) as EX.
      { eapply Forall2_inj_OOM_l; eauto.
        intros a H0 a' b H2 H3.
        pose proof DVCrev.dvalue_refine_strict_R2_injective _ _ _ _ H2 H3 as (_&?).
        forward H4; auto; subst.
      }
      subst.
      reflexivity.
    - unfold fin_to_inf_dvalue in LIFT.
      break_match_hyp; clear Heqs; destruct p; clear e0.
      break_match_hyp_inv; clear Heqs; destruct p; clear e1.
      cbn in e.
      break_match_hyp_inv.
      clear H0.
      eapply DVCrev.dvalue_convert_strict_vector_inv in e0.
      destruct e0 as (?&?&?).
      subst.
      eapply map_monad_oom_Forall2 in H1, Heqo.
      assert (elts=x) as EX.
      { eapply Forall2_inj_OOM_l; eauto.
        intros a H0 a' b H2 H3.
        pose proof DVCrev.dvalue_refine_strict_R2_injective _ _ _ _ H2 H3 as (_&?).
        forward H4; auto; subst.
      }
      subst.
      reflexivity.
  Qed.

  (* Could be the case that OOM happens...

     If uv_inf is an IBinop, for instance...

     64_bit_intmax + 1

     Then the infinite concretization will produce a value, but the
     finite concretization should OOM.
   *)
  Lemma concretize_inf_excluded_middle :
    forall uv_fin,
      (exists dv_fin,
          IS2.LLVM.MEM.CP.CONC.concretize uv_fin dv_fin) \/
          (* Should actually only be OOM in concretization... *)
          (forall dv_fin, ~ IS2.LLVM.MEM.CP.CONC.concretize uv_fin dv_fin).
  Proof.
    intros uv_fin.
    assert ((exists dv_fin : dvalue, concretize uv_fin dv_fin) \/ (~ exists dv_fin : dvalue, concretize uv_fin dv_fin)).
    apply Classical_Prop.classic.
    destruct H; auto.
    right.
    apply not_ex_all_not; eauto.
  Qed.

  Lemma concretize_fails_inf_fin :
    forall uv_inf uv_fin
      (REF : uvalue_refine_strict uv_inf uv_fin)
      (FAILS : forall dv : IS1.LP.Events.DV.dvalue, ~ IS1.LLVM.MEM.CP.CONC.concretize uv_inf dv),
    forall dv : dvalue, ~ concretize uv_fin dv.
  Proof.
    intros uv_inf uv_fin REF FAILS dv CONC.
    eapply FAILS.
    eapply uvalue_concretize_strict_concretize_inclusion; eauto.
  Qed.

  (* TODO: Move this? *)
  Ltac unfold_dvalue_refine_strict :=
    rewrite dvalue_refine_strict_equation in *; cbn in *.

  Ltac unfold_dvalue_refine_strict_goal :=
    rewrite dvalue_refine_strict_equation; cbn.

  Ltac unfold_dvalue_refine_strict_in H :=
    rewrite dvalue_refine_strict_equation in H; cbn in H.

  Ltac unfold_uvalue_refine_strict :=
    rewrite uvalue_refine_strict_equation in *; cbn in *.

  Ltac unfold_uvalue_refine_strict_goal :=
    rewrite uvalue_refine_strict_equation; cbn.

  Ltac unfold_uvalue_refine_strict_in H :=
    rewrite uvalue_refine_strict_equation in H; cbn in H.

  (* TODO: can I generalize this? *)
  (* TODO: Move this *)
  Lemma map_monad_ErrUbOomProp_ub :
    forall {A B} (f : A -> ErrUbOomProp B) l res,
      @map_monad ErrUbOomProp Monad_ErrUbOomProp _ _ f l (raise_ub res) ->
      exists a, In a l /\ f a (raise_ub res).
  Proof.
    intros A B f l b MAP.
    generalize dependent b.
    generalize dependent l.
    induction l; intros b MAP.
    - cbn in MAP.
      inv MAP.
    - cbn.
      cbn in MAP.
      repeat red in MAP.
      destruct MAP as (?&?&?&?&?).
      destruct_err_ub_oom x; subst; cbn in H0; inv H0.
      + clear H1.
        exists a; split; eauto.
      + destruct H1 as [[] | H1].
        specialize (H1 x1).
        forward H1; [cbn; auto|].
        repeat red in H1.
        destruct H1 as (?&?&?&?&?).
        rewrite <- H1 in H3.
        destruct_err_ub_oom x; subst; cbn in H1, H3; inv H3.
        * eapply IHl in H0; eauto.
          destruct H0 as (?&?&?).
          exists x.
          split; eauto.
        * destruct H2 as [[] | H2].
          specialize (H2 x3).
          forward H2; [cbn; auto|].
          rewrite <- H2 in H5.
          inv H5.
  Qed.

  (* TODO: Move this *)
  Lemma eval_int_op_ix_ub_fin_inf :
    forall sz v1 v2 iop ub_msg,
      @eval_int_op err_ub_oom (@Integers.int sz) (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@VIntVMemInt (@Integers.int sz) (@VInt_Bounded sz)) (@ToDvalue_Int sz)
        iop v1 v2 = UB_unERR_UB_OOM ub_msg ->
      @IS1.LP.Events.DV.eval_int_op err_ub_oom (@Integers.int sz)
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@VIntVMemInt (@Integers.int sz) (@VInt_Bounded sz)) (@IS1.LP.Events.DV.ToDvalue_Int sz)
        iop v1 v2 = UB_unERR_UB_OOM ub_msg.
  Proof.
    intros sz v1 v2 iop ub_msg EVAL.
    destruct iop;
      try solve
        [ cbn in *;
          repeat break_match_hyp_inv; cbn in *;
          cbn in CONV; inv CONV;
          cbn in *; reflexivity
        | cbn in *;
          repeat break_match_hyp_inv; cbn in *; inv EVAL;
          cbn in CONV; inv CONV;
          cbn in *; reflexivity
        | cbn in *;
          repeat break_match_hyp_inv; auto
        ].
  Qed.

  (* TODO: Move this *)
  Lemma eval_int_op_iptr_ub_fin_inf :
    forall v1_fin v2_fin v1_inf v2_inf iop ub_msg,
      @eval_int_op err_ub_oom IP.intptr (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        VMemInt_intptr' ToDvalue_intptr
        iop v1_fin v2_fin = UB_unERR_UB_OOM ub_msg ->
      IS1.LP.IP.from_Z (IP.to_Z v1_fin) = NoOom v1_inf ->
      IS1.LP.IP.from_Z (IP.to_Z v2_fin) = NoOom v2_inf ->
      @IS1.LP.Events.DV.eval_int_op err_ub_oom IS1.LP.IP.intptr
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        IS1.LP.Events.DV.VMemInt_intptr' IS1.LP.Events.DV.ToDvalue_intptr
        iop v1_inf v2_inf = UB_unERR_UB_OOM ub_msg.
  Proof.
    intros v1_fin v2_fin v1_inf v2_inf iop ub_msg
      EVAL LIFT1 LIFT2.

    assert (IP.to_Z v1_fin = IS1.LP.IP.to_Z v1_inf) as V1.
    { erewrite IS1.LP.IP.from_Z_to_Z; eauto. }

    assert (IP.to_Z v2_fin = IS1.LP.IP.to_Z v2_inf) as V2.
    { erewrite IS1.LP.IP.from_Z_to_Z; eauto. }

    destruct iop.
    - (* Add *)
      cbn in *.
      repeat rewrite VMEM_IP_PROP1.madd_carry_zero, VMEM_IP_PROP1.madd_overflow_zero.
      repeat rewrite VMEM_IP_PROP2.madd_carry_zero, VMEM_IP_PROP2.madd_overflow_zero in EVAL.
      setoid_rewrite VMEM_IP_PROP1.mequ_zero_one_false.
      setoid_rewrite VMEM_IP_PROP2.mequ_zero_one_false in EVAL.
      repeat rewrite Bool.andb_false_r.
      repeat rewrite Bool.andb_false_r in EVAL.
      cbn in *.

      remember (lift_OOM (madd v1_fin v2_fin)) as add_result.
      destruct_err_ub_oom add_result; inv EVAL.
      symmetry in Heqadd_result.
      destruct (madd v1_fin v2_fin) eqn:HADD; inv Heqadd_result.
    - (* Sub *)
      cbn in *.
      repeat rewrite VMEM_IP_PROP1.msub_borrow_zero, VMEM_IP_PROP1.msub_overflow_zero.
      repeat rewrite VMEM_IP_PROP2.msub_borrow_zero, VMEM_IP_PROP2.msub_overflow_zero in EVAL.
      setoid_rewrite VMEM_IP_PROP1.mequ_zero_one_false.
      setoid_rewrite VMEM_IP_PROP2.mequ_zero_one_false in EVAL.
      repeat rewrite Bool.andb_false_r.
      repeat rewrite Bool.andb_false_r in EVAL.
      cbn in *.

      remember (lift_OOM (msub v1_fin v2_fin)) as sub_result.
      destruct_err_ub_oom sub_result; inv EVAL.
      symmetry in Heqsub_result.
      destruct (msub v1_fin v2_fin) eqn:HSUB; inv Heqsub_result.
    - (* Mul *)
      cbn in *.
      destruct mbitwidth; cbn in EVAL.
      2: {
        remember (lift_OOM (mmul v1_fin v2_fin)) as mul_result.
        destruct_err_ub_oom mul_result; inv EVAL.
        symmetry in Heqmul_result.
        destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.

        cbn in H0.
        setoid_rewrite IP.VMemInt_intptr_dtyp in H0.
        setoid_rewrite dtyp_eqb_refl in H0.
        break_match_hyp_inv.
      }

      break_match_hyp_inv.

      { remember (lift_OOM (mmul v1_fin v2_fin)) as mul_result.
        destruct_err_ub_oom mul_result; inv H0.
        symmetry in Heqmul_result.
        destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.
      }

      break_match_goal.
      {
        remember (lift_OOM (mmul v1_fin v2_fin)) as mul_result.
        destruct_err_ub_oom mul_result; inv H0.
        symmetry in Heqmul_result.
        destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.
        destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.
        epose proof VMEM_REF.mmul_refine _ _ _ v1_inf v2_inf V1 V2 HMUL as (?&?&?&?).
        setoid_rewrite H.
        cbn.

        setoid_rewrite IP.VMemInt_intptr_dtyp in H1.
        rewrite dtyp_eqb_refl in H1.
        setoid_rewrite VMEM_REF.munsigned_refine in H1; eauto.
        rewrite H2 in H1.
        cbn in *.
        inv H1.
      }

      remember (lift_OOM (mmul v1_fin v2_fin)) as mul_result.
      destruct_err_ub_oom mul_result; inv H0.
      symmetry in Heqmul_result.
      destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.
      destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.
      epose proof VMEM_REF.mmul_refine _ _ _ v1_inf v2_inf V1 V2 HMUL as (?&?&?&?).
      setoid_rewrite H.
      cbn.
      setoid_rewrite H2.

      setoid_rewrite IP.VMemInt_intptr_dtyp in H1.
      setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
      rewrite dtyp_eqb_refl.
      rewrite dtyp_eqb_refl in H1.
      setoid_rewrite VMEM_REF.munsigned_refine in H1; eauto.
      rewrite H2 in H1.
      cbn in *.
      inv H1.
    - (* Shl *)
      cbn in *.
      destruct (mshl v1_fin v2_fin) eqn:HSHL;
        cbn in *; inv EVAL.

      epose proof VMEM_REF.mshl_refine _ _ _ v1_inf v2_inf V1 V2 HSHL as (?&?&?).
      setoid_rewrite H; cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in H0.
      setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
      setoid_rewrite dtyp_eqb_refl.
      setoid_rewrite dtyp_eqb_refl in H0.
      setoid_rewrite VMEM_REF.munsigned_refine in H0; eauto.
      break_match_hyp_inv.
    - (* UDiv *)
      cbn.
      cbn in EVAL.
      setoid_rewrite VMEM_REF.munsigned_refine in EVAL; eauto.
      break_match_hyp_inv.
      setoid_rewrite Heqb; auto.
      setoid_rewrite VMEM_REF.munsigned_refine in H0; eauto.
      break_match_hyp_inv;
        setoid_rewrite Heqb0;
        cbn in CONV; inv CONV.
    - (* SDiv *)
      cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL.
      setoid_rewrite dtyp_eqb_refl in EVAL.
      inv EVAL.
    - (* LShr *)
      cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL.
      setoid_rewrite dtyp_eqb_refl in EVAL.
      setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
      setoid_rewrite dtyp_eqb_refl.
      cbn in *.
      rewrite Bool.andb_false_r in *.
      setoid_rewrite VMEM_REF.munsigned_refine in EVAL; eauto.
      break_match_hyp_inv; setoid_rewrite Heqb;
        cbn in CONV; inv CONV.
    - (* AShr *)
      cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL.
      setoid_rewrite dtyp_eqb_refl in EVAL.
      inv EVAL.
    - (* URem *)
      cbn in *.
      setoid_rewrite VMEM_REF.munsigned_refine in EVAL; eauto.
      break_match_hyp_inv.
      setoid_rewrite Heqb.
      auto.
    - (* SRem *)
      cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL.
      setoid_rewrite dtyp_eqb_refl in EVAL.
      inv EVAL.
    - (* And *)
      cbn in *; inv EVAL.
    - (* Or *)
      cbn in *; inv EVAL.
    - (* Xor *)
      cbn in *; inv EVAL.
  Qed.

  Hint Resolve
    eval_int_op_ix_ub_fin_inf
    eval_int_op_iptr_ub_fin_inf
    : EVAL_INT_FIN_INF.

  (* TODO: Move this *)
  Lemma eval_int_op_ix_err_fin_inf :
    forall sz v1 v2 iop err_msg,
      @eval_int_op err_ub_oom (@Integers.int sz) (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@VIntVMemInt (@Integers.int sz) (@VInt_Bounded sz)) (@ToDvalue_Int sz)
        iop v1 v2 = ERR_unERR_UB_OOM err_msg ->
      @IS1.LP.Events.DV.eval_int_op err_ub_oom (@Integers.int sz)
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@VIntVMemInt (@Integers.int sz) (@VInt_Bounded sz)) (@IS1.LP.Events.DV.ToDvalue_Int sz)
        iop v1 v2 = ERR_unERR_UB_OOM err_msg.
  Proof.
    intros sz v1 v2 iop ub_msg EVAL.
    destruct iop;
      try solve
        [ cbn in *;
          repeat break_match_hyp_inv; cbn in *;
          cbn in CONV; inv CONV;
          cbn in *; reflexivity
        | cbn in *;
          repeat break_match_hyp_inv; cbn in *; inv EVAL;
          cbn in CONV; inv CONV;
          cbn in *; reflexivity
        | cbn in *;
          repeat break_match_hyp_inv; auto
        ].
  Qed.

  (* TODO: Move this *)
  Lemma eval_int_op_iptr_err_fin_inf :
    forall v1_fin v2_fin v1_inf v2_inf iop err_msg,
      @eval_int_op err_ub_oom IP.intptr (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        VMemInt_intptr' ToDvalue_intptr
        iop v1_fin v2_fin = ERR_unERR_UB_OOM err_msg ->
      IS1.LP.IP.from_Z (IP.to_Z v1_fin) = NoOom v1_inf ->
      IS1.LP.IP.from_Z (IP.to_Z v2_fin) = NoOom v2_inf ->
      @IS1.LP.Events.DV.eval_int_op err_ub_oom IS1.LP.IP.intptr
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        IS1.LP.Events.DV.VMemInt_intptr' IS1.LP.Events.DV.ToDvalue_intptr
        iop v1_inf v2_inf = ERR_unERR_UB_OOM err_msg.
  Proof.
    intros v1_fin v2_fin v1_inf v2_inf iop err_msg
      EVAL LIFT1 LIFT2.

    assert (IP.to_Z v1_fin = IS1.LP.IP.to_Z v1_inf) as V1.
    { erewrite IS1.LP.IP.from_Z_to_Z; eauto. }

    assert (IP.to_Z v2_fin = IS1.LP.IP.to_Z v2_inf) as V2.
    { erewrite IS1.LP.IP.from_Z_to_Z; eauto. }

    destruct iop.
    - (* Add *)
      cbn in *.
      repeat rewrite VMEM_IP_PROP1.madd_carry_zero, VMEM_IP_PROP1.madd_overflow_zero.
      repeat rewrite VMEM_IP_PROP2.madd_carry_zero, VMEM_IP_PROP2.madd_overflow_zero in EVAL.
      setoid_rewrite VMEM_IP_PROP1.mequ_zero_one_false.
      setoid_rewrite VMEM_IP_PROP2.mequ_zero_one_false in EVAL.
      repeat rewrite Bool.andb_false_r.
      repeat rewrite Bool.andb_false_r in EVAL.
      cbn in *.

      remember (lift_OOM (madd v1_fin v2_fin)) as add_result.
      destruct_err_ub_oom add_result; inv EVAL.
      symmetry in Heqadd_result.
      destruct (madd v1_fin v2_fin) eqn:HADD; inv Heqadd_result.
    - (* Sub *)
      cbn in *.
      repeat rewrite VMEM_IP_PROP1.msub_borrow_zero, VMEM_IP_PROP1.msub_overflow_zero.
      repeat rewrite VMEM_IP_PROP2.msub_borrow_zero, VMEM_IP_PROP2.msub_overflow_zero in EVAL.
      setoid_rewrite VMEM_IP_PROP1.mequ_zero_one_false.
      setoid_rewrite VMEM_IP_PROP2.mequ_zero_one_false in EVAL.
      repeat rewrite Bool.andb_false_r.
      repeat rewrite Bool.andb_false_r in EVAL.
      cbn in *.

      remember (lift_OOM (msub v1_fin v2_fin)) as sub_result.
      destruct_err_ub_oom sub_result; inv EVAL.
      symmetry in Heqsub_result.
      destruct (msub v1_fin v2_fin) eqn:HSUB; inv Heqsub_result.
    - (* Mul *)
      cbn in *.
      destruct mbitwidth; cbn in EVAL.
      2: {
        remember (lift_OOM (mmul v1_fin v2_fin)) as mul_result.
        destruct_err_ub_oom mul_result; inv EVAL.
        symmetry in Heqmul_result.
        destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.

        cbn in H0.
        setoid_rewrite IP.VMemInt_intptr_dtyp in H0.
        setoid_rewrite dtyp_eqb_refl in H0.
        break_match_hyp_inv.
      }

      break_match_hyp_inv.

      { remember (lift_OOM (mmul v1_fin v2_fin)) as mul_result.
        destruct_err_ub_oom mul_result; inv H0.
        symmetry in Heqmul_result.
        destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.
      }

      break_match_goal.
      {
        remember (lift_OOM (mmul v1_fin v2_fin)) as mul_result.
        destruct_err_ub_oom mul_result; inv H0.
        symmetry in Heqmul_result.
        destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.
        destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.
        epose proof VMEM_REF.mmul_refine _ _ _ v1_inf v2_inf V1 V2 HMUL as (?&?&?&?).
        setoid_rewrite H.
        cbn.

        setoid_rewrite IP.VMemInt_intptr_dtyp in H1.
        rewrite dtyp_eqb_refl in H1.
        setoid_rewrite VMEM_REF.munsigned_refine in H1; eauto.
        rewrite H2 in H1.
        cbn in *.
        inv H1.
      }

      remember (lift_OOM (mmul v1_fin v2_fin)) as mul_result.
      destruct_err_ub_oom mul_result; inv H0.
      symmetry in Heqmul_result.
      destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.
      destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.
      epose proof VMEM_REF.mmul_refine _ _ _ v1_inf v2_inf V1 V2 HMUL as (?&?&?&?).
      setoid_rewrite H.
      cbn.
      setoid_rewrite H2.

      setoid_rewrite IP.VMemInt_intptr_dtyp in H1.
      setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
      rewrite dtyp_eqb_refl.
      rewrite dtyp_eqb_refl in H1.
      setoid_rewrite VMEM_REF.munsigned_refine in H1; eauto.
      rewrite H2 in H1.
      cbn in *.
      inv H1.
    - (* Shl *)
      cbn in *.
      destruct (mshl v1_fin v2_fin) eqn:HSHL;
        cbn in *; inv EVAL.

      epose proof VMEM_REF.mshl_refine _ _ _ v1_inf v2_inf V1 V2 HSHL as (?&?&?).
      setoid_rewrite H; cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in H0.
      setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
      setoid_rewrite dtyp_eqb_refl.
      setoid_rewrite dtyp_eqb_refl in H0.
      setoid_rewrite VMEM_REF.munsigned_refine in H0; eauto.
      break_match_hyp_inv.
    - (* UDiv *)
      cbn.
      cbn in EVAL.
      setoid_rewrite VMEM_REF.munsigned_refine in EVAL; eauto.
      break_match_hyp_inv.
      setoid_rewrite Heqb; auto.
      setoid_rewrite VMEM_REF.munsigned_refine in H0; eauto.
      break_match_hyp_inv;
        setoid_rewrite Heqb0;
        cbn in CONV; inv CONV.
    - (* SDiv *)
      cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL.
      setoid_rewrite dtyp_eqb_refl in EVAL.
      setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
      setoid_rewrite dtyp_eqb_refl.
      inv EVAL.
      reflexivity.
    - (* LShr *)
      cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL.
      setoid_rewrite dtyp_eqb_refl in EVAL.
      setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
      setoid_rewrite dtyp_eqb_refl.
      cbn in *.
      rewrite Bool.andb_false_r in *.
      setoid_rewrite VMEM_REF.munsigned_refine in EVAL; eauto.
      break_match_hyp_inv; setoid_rewrite Heqb;
        cbn in CONV; inv CONV.
    - (* AShr *)
      cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL.
      setoid_rewrite dtyp_eqb_refl in EVAL.
      setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
      setoid_rewrite dtyp_eqb_refl.
      inv EVAL.
      reflexivity.
    - (* URem *)
      cbn in *.
      setoid_rewrite VMEM_REF.munsigned_refine in EVAL; eauto.
      break_match_hyp_inv.
    - (* SRem *)
      cbn in *.
      setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL.
      setoid_rewrite dtyp_eqb_refl in EVAL.
      setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
      setoid_rewrite dtyp_eqb_refl.
      inv EVAL.
      reflexivity.
    - (* And *)
      cbn in *; inv EVAL.
    - (* Or *)
      cbn in *; inv EVAL.
    - (* Xor *)
      cbn in *; inv EVAL.
  Qed.

  Hint Resolve
    eval_int_op_ix_err_fin_inf
    eval_int_op_iptr_err_fin_inf
    : EVAL_INT_FIN_INF.

  Lemma vec_loop_ub_fin_inf :
    forall f_fin f_inf xs ys ub_msg,
      (forall dv1_fin dv2_fin res_fin dv1_inf dv2_inf,
          f_fin dv1_fin dv2_fin = ret res_fin ->
          fin_to_inf_dvalue dv1_fin = dv1_inf ->
          fin_to_inf_dvalue dv2_fin = dv2_inf ->
          f_inf dv1_inf dv2_inf = ret (fin_to_inf_dvalue res_fin)) ->
      (forall dv1_fin dv2_fin ub_msg dv1_inf dv2_inf,
          f_fin dv1_fin dv2_fin = UB_unERR_UB_OOM ub_msg ->
          fin_to_inf_dvalue dv1_fin = dv1_inf ->
          fin_to_inf_dvalue dv2_fin = dv2_inf ->
          f_inf dv1_inf dv2_inf = UB_unERR_UB_OOM ub_msg) ->
      @vec_loop _ err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) f_fin (combine xs ys) = UB_unERR_UB_OOM ub_msg ->
      @IS1.LP.Events.DV.vec_loop _ err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) f_inf (combine (map fin_to_inf_dvalue xs) (map fin_to_inf_dvalue ys)) = UB_unERR_UB_OOM ub_msg.
  Proof.
    intros f_fin f_inf xs ys res SUCCESS UB RES.

    remember (xs, ys) as ZIP.
    replace xs with (fst ZIP) by (subst; cbn; auto).
    replace ys with (snd ZIP) by (subst; cbn; auto).
    replace xs with (fst ZIP) in RES by (subst; cbn; auto).
    replace ys with (snd ZIP) in RES by (subst; cbn; auto).
    clear HeqZIP xs ys.

    generalize dependent res.
    induction ZIP using double_list_rect; intros res RES;
      try solve [cbn in *; inv RES; auto].
    - (* Both cons *)
      unfold fst, snd in *.
      repeat rewrite map_cons.
      repeat rewrite combine_cons.
      repeat rewrite vec_loop_cons.
      rewrite combine_cons in RES.
      rewrite vec_loop_cons in RES.
      cbn in RES.
      remember (@vec_loop DVCrev.DV1.dvalue err_ub_oom
                  (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) f_fin
                  (@combine DVCrev.DV1.dvalue DVCrev.DV1.dvalue xs ys)) as res'.
      destruct_err_ub_oom res';
        cbn in RES; inv RES;
        symmetry in Heqres'.
      { specialize (IHZIP res eq_refl).
        unfold IS1.LP.Events.DV.vec_loop in *.
        unfold vec_loop.
        rewrite IHZIP; reflexivity.
      }


      clear IHZIP.
      remember (f_fin x y) as fin.
      destruct_err_ub_oom fin; inv H0.
      erewrite vec_loop_fin_inf; eauto.
      2: apply Heqres'.
      cbn.

      erewrite UB; cbn; eauto.
  Qed.

  Lemma vec_loop_err_fin_inf :
    forall f_fin f_inf xs ys err_msg,
      (forall dv1_fin dv2_fin res_fin dv1_inf dv2_inf,
          f_fin dv1_fin dv2_fin = ret res_fin ->
          fin_to_inf_dvalue dv1_fin = dv1_inf ->
          fin_to_inf_dvalue dv2_fin = dv2_inf ->
          f_inf dv1_inf dv2_inf = ret (fin_to_inf_dvalue res_fin)) ->
      (forall dv1_fin dv2_fin ub_msg dv1_inf dv2_inf,
          f_fin dv1_fin dv2_fin = ERR_unERR_UB_OOM ub_msg ->
          fin_to_inf_dvalue dv1_fin = dv1_inf ->
          fin_to_inf_dvalue dv2_fin = dv2_inf ->
          f_inf dv1_inf dv2_inf = ERR_unERR_UB_OOM ub_msg) ->
      @vec_loop _ err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) f_fin (combine xs ys) = ERR_unERR_UB_OOM err_msg ->
      @IS1.LP.Events.DV.vec_loop _ err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) f_inf (combine (map fin_to_inf_dvalue xs) (map fin_to_inf_dvalue ys)) = ERR_unERR_UB_OOM err_msg.
  Proof.
    intros f_fin f_inf xs ys res SUCCESS UB RES.

    remember (xs, ys) as ZIP.
    replace xs with (fst ZIP) by (subst; cbn; auto).
    replace ys with (snd ZIP) by (subst; cbn; auto).
    replace xs with (fst ZIP) in RES by (subst; cbn; auto).
    replace ys with (snd ZIP) in RES by (subst; cbn; auto).
    clear HeqZIP xs ys.

    generalize dependent res.
    induction ZIP using double_list_rect; intros res RES;
      try solve [cbn in *; inv RES; auto].
    - (* Both cons *)
      unfold fst, snd in *.
      repeat rewrite map_cons.
      repeat rewrite combine_cons.
      repeat rewrite vec_loop_cons.
      rewrite combine_cons in RES.
      rewrite vec_loop_cons in RES.
      cbn in RES.
      remember (@vec_loop DVCrev.DV1.dvalue err_ub_oom
                  (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) f_fin
                  (@combine DVCrev.DV1.dvalue DVCrev.DV1.dvalue xs ys)) as res'.
      destruct_err_ub_oom res';
        cbn in RES; inv RES;
        symmetry in Heqres'.
      { specialize (IHZIP res eq_refl).
        unfold IS1.LP.Events.DV.vec_loop in *.
        unfold vec_loop.
        rewrite IHZIP; reflexivity.
      }


      clear IHZIP.
      remember (f_fin x y) as fin.
      destruct_err_ub_oom fin; inv H0.
      erewrite vec_loop_fin_inf; eauto.
      2: apply Heqres'.
      cbn.

      erewrite UB; cbn; eauto.
  Qed.

  (* TODO: Move this / generalize monad? *)
  Lemma eval_iop_integer_h_ub_fin_inf :
    forall dv1_fin dv2_fin ub_msg iop dv1_inf dv2_inf,
      @eval_iop_integer_h err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        iop dv1_fin dv2_fin = UB_unERR_UB_OOM ub_msg ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @IS1.LP.Events.DV.eval_iop_integer_h err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        iop dv1_inf dv2_inf = UB_unERR_UB_OOM ub_msg.
  Proof.
    intros dv1_fin dv2_fin ub_msg iop dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    unfold eval_iop_integer_h in EVAL.
    (* Nasty case analysis... *)
    repeat break_match_hyp_inv;
      rewrite_fin_to_inf_dvalue;
      cbn;
      try setoid_rewrite Heqb; eauto with EVAL_INT_FIN_INF.

    { (* dv1: ix *)
      unfold intptr_fin_inf.
      repeat break_match_goal; try contradiction.
      dependent destruction e; cbn in *; subst.
      eapply eval_int_op_ix_ub_fin_inf; eauto.
    }

    { (* dv1: iptr *)
      unfold intptr_fin_inf.
      repeat break_match_goal.
      clear Heqs Heqs0.
      eapply eval_int_op_iptr_ub_fin_inf; eauto.
    }
  Qed.

  Hint Resolve eval_iop_integer_h_ub_fin_inf : EVAL_INT_FIN_INF.

  (* TODO: Move this / generalize monad? *)
  Lemma eval_iop_integer_h_err_fin_inf :
    forall dv1_fin dv2_fin ub_msg iop dv1_inf dv2_inf,
      @eval_iop_integer_h err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        iop dv1_fin dv2_fin = ERR_unERR_UB_OOM ub_msg ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @IS1.LP.Events.DV.eval_iop_integer_h err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        iop dv1_inf dv2_inf = ERR_unERR_UB_OOM ub_msg.
  Proof.
    intros dv1_fin dv2_fin ub_msg iop dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    unfold eval_iop_integer_h in EVAL.
    (* Nasty case analysis... *)
    repeat break_match_hyp_inv;
      rewrite_fin_to_inf_dvalue;
      cbn;
      try setoid_rewrite Heqb; eauto with EVAL_INT_FIN_INF.

    { (* dv1: ix *)
      unfold intptr_fin_inf.
      repeat break_match_goal; try contradiction.
      dependent destruction e; cbn in *; subst.
      eapply eval_int_op_ix_err_fin_inf; eauto.
    }

    { (* dv1: ix *)
      unfold intptr_fin_inf.
      repeat break_match_goal; try contradiction; auto.
    }

    { (* dv1: iptr *)
      unfold intptr_fin_inf.
      repeat break_match_goal.
      clear Heqs Heqs0.
      eapply eval_int_op_iptr_err_fin_inf; eauto.
    }
  Qed.

  Hint Resolve eval_iop_integer_h_err_fin_inf : EVAL_INT_FIN_INF.

  (* TODO: Move this / generalize monad? *)
  Lemma eval_iop_ub_fin_inf :
    forall dv1_fin dv2_fin ub_msg iop dv1_inf dv2_inf,
      @eval_iop err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        iop dv1_fin dv2_fin = UB_unERR_UB_OOM ub_msg ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @IS1.LP.Events.DV.eval_iop err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        iop dv1_inf dv2_inf = UB_unERR_UB_OOM ub_msg.
  Proof.
    intros dv1_fin dv2_fin res_fin iop dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    unfold eval_iop in EVAL.
    (* Nasty case analysis... *)
    repeat break_match_hyp_inv;
      rewrite_fin_to_inf_dvalue;
      cbn;
      try setoid_rewrite Heqb; eauto with EVAL_INT_FIN_INF.

    { (* dv1: ix *)
      unfold intptr_fin_inf.
      repeat break_match_goal; try contradiction.
      dependent destruction e; cbn in *; subst.
      eapply eval_int_op_ix_ub_fin_inf; eauto.
    }

    { (* dv1: iptr *)
      unfold fin_to_inf_dvalue.
      unfold intptr_fin_inf.
      repeat break_match_goal.
      clear Heqs Heqs0.
      eapply eval_int_op_iptr_ub_fin_inf; eauto.
    }

    { (* dv1: Vector *)
      (* dv2 is also a vector *)
      remember (vec_loop (eval_iop_integer_h iop) (combine elts elts0)) as res.
      destruct_err_ub_oom res; cbn in *; inv Heqs; inv Heqe; inv H0.

      symmetry in Heqres.
      erewrite vec_loop_ub_fin_inf; cbn; eauto.

      intros dv1_fin dv2_fin res_fin' dv1_inf dv2_inf H H0 H1.
      eapply eval_iop_integer_h_fin_inf; eauto.

      intros dv1_fin dv2_fin ub_msg dv1_inf dv2_inf H H0 H1.
      eapply eval_iop_integer_h_ub_fin_inf; eauto.
    }
  Qed.

  (* TODO: Move this / generalize monad? *)
  Lemma eval_iop_err_fin_inf :
    forall dv1_fin dv2_fin err_msg iop dv1_inf dv2_inf,
      @eval_iop err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        iop dv1_fin dv2_fin = ERR_unERR_UB_OOM err_msg ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @IS1.LP.Events.DV.eval_iop err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        iop dv1_inf dv2_inf = ERR_unERR_UB_OOM err_msg.
  Proof.
    intros dv1_fin dv2_fin res_fin iop dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    unfold eval_iop in EVAL.
    (* Nasty case analysis... *)
    repeat break_match_hyp_inv;
      rewrite_fin_to_inf_dvalue;
      cbn;
      try setoid_rewrite Heqb; eauto with EVAL_INT_FIN_INF.

    { (* dv1: ix *)
      unfold intptr_fin_inf.
      repeat break_match_goal; try contradiction.
      dependent destruction e; cbn in *; subst.
      eapply eval_int_op_ix_err_fin_inf; eauto.
    }

    { (* dv1: ix *)
      unfold intptr_fin_inf.
      repeat break_match_goal; try contradiction; auto.
    }

    { (* dv1: iptr *)
      unfold fin_to_inf_dvalue.
      unfold intptr_fin_inf.
      repeat break_match_goal.
      clear Heqs Heqs0.
      eapply eval_int_op_iptr_err_fin_inf; eauto.
    }

    { (* dv1: Vector *)
      (* dv2 is also a vector *)
      remember (vec_loop (eval_iop_integer_h iop) (combine elts elts0)) as res.
      destruct_err_ub_oom res; cbn in *; inv Heqs; inv Heqe; inv H0.

      symmetry in Heqres.
      erewrite vec_loop_err_fin_inf; cbn; eauto.

      intros dv1_fin dv2_fin res_fin' dv1_inf dv2_inf H H0 H1.
      eapply eval_iop_integer_h_fin_inf; eauto.

      intros dv1_fin dv2_fin ub_msg dv1_inf dv2_inf H H0 H1.
      eapply eval_iop_integer_h_err_fin_inf; eauto.
    }
  Qed.

  Hint Resolve eval_iop_ub_fin_inf : EVAL_INT_FIN_INF.
  Hint Resolve eval_iop_err_fin_inf : EVAL_INT_FIN_INF.

  Lemma eval_int_icmp_ub_fin_inf :
    forall {Int} {VMInt : VellvmIntegers.VMemInt Int} icmp a b ub_msg,
      @eval_int_icmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) Int VMInt icmp a b = UB_unERR_UB_OOM ub_msg  ->
      @IS1.LP.Events.DV.eval_int_icmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) Int VMInt icmp a b = UB_unERR_UB_OOM ub_msg.
  Proof.
    intros Int VMInt icmp a b ub_msg FIN.
    Transparent eval_int_icmp IS1.LP.Events.DV.eval_int_icmp.
    unfold eval_int_icmp, IS1.LP.Events.DV.eval_int_icmp.
    destruct icmp;
      try solve
        [ cbn in *;
          break_match_hyp_inv;
          rewrite_fin_to_inf_dvalue;
          eauto
        | cbn in *;
          repeat break_match_hyp_inv; inv Heqs;
          cbn;
          break_match_goal;
          rewrite_fin_to_inf_dvalue; auto
        ].
  Qed.

  (* TODO: Move this *)
  Lemma eval_int_icmp_iptr_ub_fin_inf :
    forall v1_fin v2_fin v1_inf v2_inf icmp ub_msg,
      @eval_int_icmp err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        IP.intptr
        VMemInt_intptr'
        icmp v1_fin v2_fin = UB_unERR_UB_OOM ub_msg ->
      IS1.LP.IP.from_Z (IP.to_Z v1_fin) = NoOom v1_inf ->
      IS1.LP.IP.from_Z (IP.to_Z v2_fin) = NoOom v2_inf ->
      @IS1.LP.Events.DV.eval_int_icmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        IS1.LP.IP.intptr
        IS1.LP.Events.DV.VMemInt_intptr'
        icmp v1_inf v2_inf = UB_unERR_UB_OOM ub_msg.
  Proof.
    intros v1_fin v2_fin v1_inf v2_inf icmp ub_msg EVAL LIFT1 LIFT2.

    assert (IP.to_Z v1_fin = IS1.LP.IP.to_Z v1_inf) as V1.
    { erewrite IS1.LP.IP.from_Z_to_Z; eauto. }

    assert (IP.to_Z v2_fin = IS1.LP.IP.to_Z v2_inf) as V2.
    { erewrite IS1.LP.IP.from_Z_to_Z; eauto. }

    destruct icmp;
      try
        solve
        [ cbn in *;
          erewrite <- VMEM_REF.mcmpu_refine; eauto;
          break_match_hyp_inv;
          setoid_rewrite Heqb;
          cbn in CONV; inv CONV; auto
        | cbn in *;
          setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL;
          setoid_rewrite dtyp_eqb_refl in EVAL;
          inv EVAL
        ].
  Qed.

  (* TODO: Move this *)
  Lemma eval_int_icmp_iptr_err_fin_inf :
    forall v1_fin v2_fin v1_inf v2_inf icmp err_msg,
      @eval_int_icmp err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        IP.intptr
        VMemInt_intptr'
        icmp v1_fin v2_fin = ERR_unERR_UB_OOM err_msg ->
      IS1.LP.IP.from_Z (IP.to_Z v1_fin) = NoOom v1_inf ->
      IS1.LP.IP.from_Z (IP.to_Z v2_fin) = NoOom v2_inf ->
      @IS1.LP.Events.DV.eval_int_icmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        IS1.LP.IP.intptr
        IS1.LP.Events.DV.VMemInt_intptr'
        icmp v1_inf v2_inf = ERR_unERR_UB_OOM err_msg.
  Proof.
    intros v1_fin v2_fin v1_inf v2_inf icmp err_msg EVAL LIFT1 LIFT2.

    assert (IP.to_Z v1_fin = IS1.LP.IP.to_Z v1_inf) as V1.
    { erewrite IS1.LP.IP.from_Z_to_Z; eauto. }

    assert (IP.to_Z v2_fin = IS1.LP.IP.to_Z v2_inf) as V2.
    { erewrite IS1.LP.IP.from_Z_to_Z; eauto. }

    destruct icmp;
      try
        solve
        [ cbn in *;
          erewrite <- VMEM_REF.mcmpu_refine; eauto;
          break_match_hyp_inv;
          setoid_rewrite Heqb;
          cbn in CONV; inv CONV; auto
        | cbn in *;
          setoid_rewrite IP.VMemInt_intptr_dtyp in EVAL;
          setoid_rewrite dtyp_eqb_refl in EVAL;
          setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp;
          setoid_rewrite dtyp_eqb_refl;
          inv EVAL;
          auto
        ].
  Qed.

  (* TODO: Move this / generalize monad? *)
  Lemma eval_icmp_ub_fin_inf :
    forall dv1_fin dv2_fin ub_msg icmp dv1_inf dv2_inf,
      @eval_icmp err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        icmp dv1_fin dv2_fin = UB_unERR_UB_OOM ub_msg ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @IS1.MEM.CP.CONC.eval_icmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        icmp dv1_inf dv2_inf = UB_unERR_UB_OOM ub_msg.
  Proof.
    intros dv1_fin dv2_fin ub_msg icmp dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    Opaque IS1.LP.Events.DV.eval_int_icmp
      eval_int_icmp.
    unfold eval_icmp in EVAL.
    (* Nasty case analysis... *)
    break_match_hyp_inv;
      try solve
        [ (* Simple integer cases *)
          break_match_hyp_inv;
          repeat rewrite_fin_to_inf_dvalue;
          cbn;
          auto;
          eapply eval_int_icmp_ub_fin_inf in H1;
          auto
        ].

    { (* dv1: addr *)
      break_match_hyp_inv.
      repeat rewrite_fin_to_inf_dvalue.
      cbn.
      eapply eval_int_icmp_ub_fin_inf in H1.
      repeat rewrite ptr_to_int_fin_to_inf_addr.
      auto.
    }

    { (* dv1: ix *)
      unfold intptr_fin_inf.
      repeat break_match_hyp_inv; try contradiction; cbn in *; subst.
      repeat rewrite_fin_to_inf_dvalue; cbn.
      unfold IS1.MEM.CP.CONC.eval_icmp.
      break_match_goal; try contradiction.
      dependent destruction e; cbn.
      eapply eval_int_icmp_ub_fin_inf; eauto.
    }

    { (* dv1: iptr *)
      break_match_hyp_inv.
      repeat rewrite_fin_to_inf_dvalue.
      cbn.
      unfold intptr_fin_inf.
      do 2 break_match_goal.
      clear Heqs Heqs0.
      eapply eval_int_icmp_iptr_ub_fin_inf in H1; eauto.
    }
  Qed.

  Lemma eval_int_icmp_err_fin_inf :
    forall {Int} {VMInt : VellvmIntegers.VMemInt Int} icmp a b err_msg,
      @eval_int_icmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) Int VMInt icmp a b = ERR_unERR_UB_OOM err_msg  ->
      @IS1.LP.Events.DV.eval_int_icmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) Int VMInt icmp a b = ERR_unERR_UB_OOM err_msg.
  Proof.
    intros Int VMInt icmp a b err_msg FIN.
    Transparent eval_int_icmp IS1.LP.Events.DV.eval_int_icmp.
    unfold eval_int_icmp, IS1.LP.Events.DV.eval_int_icmp.
    destruct icmp;
      try solve
        [ cbn in *;
          break_match_hyp_inv;
          rewrite_fin_to_inf_dvalue;
          eauto
        | cbn in *;
          repeat break_match_hyp_inv; inv Heqs;
          cbn;
          break_match_goal;
          rewrite_fin_to_inf_dvalue;
          auto
        | cbn in *; repeat break_match_hyp_inv; inv Heqs; cbn; auto
        ].
  Qed.

  Lemma show_dvalue_fin_inf_helper :
    forall fields,
      (forall dv,
          In dv fields ->
          show_dvalue dv = IS1.LP.Events.DV.show_dvalue (fin_to_inf_dvalue dv)) ->
      map show_dvalue fields = map IS1.LP.Events.DV.show_dvalue (map fin_to_inf_dvalue fields).
  Proof.
    induction fields; intros SHOW.
    - reflexivity.
    - repeat rewrite map_cons.
      rewrite SHOW; cbn; auto.
      rewrite IHfields; eauto.
      intros dv H.
      eapply SHOW.
      right; auto.
  Qed.

  Lemma show_dvalue_fin_inf :
    forall dv,
      show_dvalue dv = IS1.LP.Events.DV.show_dvalue (fin_to_inf_dvalue dv).
  Proof.
    intros dv.
    induction dv; cbn; rewrite_fin_to_inf_dvalue; cbn; auto;
      rewrite show_dvalue_fin_inf_helper; auto.
  Qed.

  (* TODO: Move this / generalize monad? *)
  Lemma eval_icmp_err_fin_inf :
    forall dv1_fin dv2_fin err_msg icmp dv1_inf dv2_inf,
      @eval_icmp err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        icmp dv1_fin dv2_fin = ERR_unERR_UB_OOM err_msg ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @IS1.MEM.CP.CONC.eval_icmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        icmp dv1_inf dv2_inf = ERR_unERR_UB_OOM err_msg.
  Proof.
    intros dv1_fin dv2_fin err_msg icmp dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    Opaque IS1.LP.Events.DV.eval_int_icmp
      eval_int_icmp
      IS1.LP.Events.DV.show_dvalue
      show_dvalue.

    unfold eval_icmp in EVAL.
    (* Nasty case analysis... *)
    break_match_hyp_inv;
      try solve
        [ (* Simple integer cases *)
          break_match_hyp_inv;
          try repeat setoid_rewrite <- show_dvalue_fin_inf;
          repeat rewrite_fin_to_inf_dvalue;
          cbn;
          repeat rewrite show_dvalue_fin_inf;
          repeat rewrite_fin_to_inf_dvalue;
          cbn;
          auto;
          eapply eval_int_icmp_err_fin_inf in H1;
          auto
        ].

    { (* dv1: addr *)
      break_match_hyp_inv; cbn in *;
        try repeat setoid_rewrite <- show_dvalue_fin_inf;
        repeat rewrite_fin_to_inf_dvalue;
        cbn;
        repeat rewrite show_dvalue_fin_inf;
        repeat rewrite_fin_to_inf_dvalue;
        try reflexivity;
        eapply eval_int_icmp_err_fin_inf in H1;
        repeat rewrite ptr_to_int_fin_to_inf_addr;
        auto.
    }

    { (* dv1: ix *)
      break_match_hyp_inv;
        try repeat setoid_rewrite <- show_dvalue_fin_inf;
        repeat rewrite_fin_to_inf_dvalue;
        cbn;
        repeat rewrite show_dvalue_fin_inf;
        repeat rewrite_fin_to_inf_dvalue;
        try reflexivity;
        repeat rewrite_fin_to_inf_dvalue.
      cbn.
      unfold intptr_fin_inf.
      unfold IS1.MEM.CP.CONC.eval_icmp.
      break_match_hyp_inv; cbn in *; try contradiction; try reflexivity.
      eapply eval_int_icmp_err_fin_inf in H0; eauto.
    }

    { (* dv1: iptr *)
      break_match_hyp_inv;
        try repeat setoid_rewrite <- show_dvalue_fin_inf;
        repeat rewrite_fin_to_inf_dvalue;
        cbn;
        repeat rewrite show_dvalue_fin_inf;
        repeat rewrite_fin_to_inf_dvalue;
        try reflexivity;
        repeat rewrite_fin_to_inf_dvalue.
      cbn.
      unfold intptr_fin_inf.
      do 2 break_match_goal.
      clear Heqs Heqs0.
      eapply eval_int_icmp_iptr_err_fin_inf in H1; eauto.
    }
  Qed.

  Lemma double_op_ub_fin_inf :
    forall fop a b ub_msg,
      double_op fop a b = UB_unERR_UB_OOM ub_msg ->
      IS1.LP.Events.DV.double_op fop a b = UB_unERR_UB_OOM ub_msg.
  Proof.
    intros fop a b ub_msg EVAL.
    destruct fop; cbn in *; inv EVAL.
  Qed.

  Lemma float_op_ub_fin_inf :
    forall fop a b ub_msg,
      float_op fop a b = UB_unERR_UB_OOM ub_msg ->
      IS1.LP.Events.DV.float_op fop a b = UB_unERR_UB_OOM ub_msg.
  Proof.
    intros fop a b ub_msg EVAL.
    destruct fop; cbn in *; inv EVAL.
  Qed.

  Lemma double_op_err_fin_inf :
    forall fop a b err_msg,
      double_op fop a b = ERR_unERR_UB_OOM err_msg ->
      IS1.LP.Events.DV.double_op fop a b = ERR_unERR_UB_OOM err_msg.
  Proof.
    intros fop a b err_msg EVAL.
    destruct fop; cbn in *; inv EVAL; auto.
  Qed.

  Lemma float_op_err_fin_inf :
    forall fop a b err_msg,
      float_op fop a b = ERR_unERR_UB_OOM err_msg ->
      IS1.LP.Events.DV.float_op fop a b = ERR_unERR_UB_OOM err_msg.
  Proof.
    intros fop a b err_msg EVAL.
    destruct fop; cbn in *; inv EVAL; auto.
  Qed.

  (* TODO: Move this / generalize monad? *)
  Lemma eval_fop_ub_fin_inf :
    forall dv1_fin dv2_fin ub_msg fop dv1_inf dv2_inf,
      @eval_fop err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        fop dv1_fin dv2_fin = UB_unERR_UB_OOM ub_msg ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @IS1.LP.Events.DV.eval_fop err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        fop dv1_inf dv2_inf = UB_unERR_UB_OOM ub_msg.
  Proof.
    intros dv1_fin dv2_fin ub_msg fop dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    unfold eval_fop in EVAL.
    (* Nasty case analysis... *)
    break_match_hyp_inv.
    { (* dv1: Double *)
      break_match_hyp_inv.
      2: {
        break_match_hyp_inv.
        unfold fin_to_inf_dvalue.
        break_match_goal; clear Heqs; destruct p; clear e0.
        break_match_goal; clear Heqs; destruct p; clear e1.
        inv e; inv e0.
        cbn.

        (* These should be the same... *)
        unfold IS1.LP.Events.DV.fop_is_div.
        unfold fop_is_div in Heqb.
        rewrite Heqb.
        reflexivity.
      }

      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs; destruct p; clear e0.
      break_match_goal; clear Heqs; destruct p; clear e1.
      inv e; inv e0.
      cbn.
      eapply double_op_ub_fin_inf; eauto.
    }

    { (* dv1: Float *)
      break_match_hyp_inv.
      2: {
        break_match_hyp_inv.
        unfold fin_to_inf_dvalue.
        break_match_goal; clear Heqs; destruct p; clear e0.
        break_match_goal; clear Heqs; destruct p; clear e1.
        inv e; inv e0.
        cbn.

        (* These should be the same... *)
        unfold IS1.LP.Events.DV.fop_is_div.
        unfold fop_is_div in Heqb.
        rewrite Heqb.
        reflexivity.
      }

      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs; destruct p; clear e0.
      break_match_goal; clear Heqs; destruct p; clear e1.
      inv e; inv e0.
      cbn.
      eapply float_op_ub_fin_inf; eauto.
    }
  Qed.

  Lemma ceres_to_sexp_fin_inf :
    forall dv_fin dv_inf,
      dvalue_refine_strict dv_inf dv_fin ->
      CeresSerialize.to_sexp dv_fin = CeresSerialize.to_sexp dv_inf.
  Proof.
    induction dv_fin using DV2.dvalue_strong_ind;
      intros dv_inf REF;
      try dvalue_refine_strict_inv REF;
      try reflexivity.

    destruct dv_fin;
      try dvalue_refine_strict_inv REF;
      try reflexivity.

    - (* Structs *)
      cbn.
      assert ((map
         (fun x0 : E2.DV.dvalue =>
            CeresS.List [CeresSerialize.to_sexp x0; CeresS.Atom_ (CeresS.Raw ",")]) fields) =
                (map
         (fun x0 : E1.DV.dvalue =>
            CeresS.List [CeresSerialize.to_sexp x0; CeresS.Atom_ (CeresS.Raw ",")]) x)).
      { generalize dependent fields.
        induction x; intros fields H H1;
          cbn in H1; inv H1; auto.

        repeat break_match_hyp_inv.
        cbn.
        erewrite H; eauto.
        2: repeat constructor.

        rewrite IHx; eauto.

        intros u H0 dv_inf H1.
        eapply H; eauto.
        clear - H0.
        dependent induction H0.
        - inv H.
          constructor.
          constructor.
          right; auto.
        - specialize (IHclos_trans2 _ eq_refl).
          eapply t_trans.
          apply H0_.
          apply IHclos_trans2.        
      }

      rewrite H0.
      reflexivity.
    - (* Packed structs *)
      cbn.
      assert ((map
         (fun x0 : E2.DV.dvalue =>
            CeresS.List [CeresSerialize.to_sexp x0; CeresS.Atom_ (CeresS.Raw ",")]) fields) =
                (map
         (fun x0 : E1.DV.dvalue =>
            CeresS.List [CeresSerialize.to_sexp x0; CeresS.Atom_ (CeresS.Raw ",")]) x)).
      { generalize dependent fields.
        induction x; intros fields H H1;
          cbn in H1; inv H1; auto.

        repeat break_match_hyp_inv.
        cbn.
        erewrite H; eauto.
        2: repeat constructor.

        rewrite IHx; eauto.

        intros u H0 dv_inf H1.
        eapply H; eauto.
        clear - H0.
        dependent induction H0.
        - inv H.
          constructor.
          constructor.
          right; auto.
        - specialize (IHclos_trans2 _ eq_refl).
          eapply t_trans.
          apply H0_.
          apply IHclos_trans2.        
      }

      rewrite H0.
      reflexivity.
    - (* Arrays *)
      cbn.
      assert ((map
         (fun x0 : E2.DV.dvalue =>
            CeresS.List [CeresSerialize.to_sexp x0; CeresS.Atom_ (CeresS.Raw ",")]) elts) =
                (map
         (fun x0 : E1.DV.dvalue =>
            CeresS.List [CeresSerialize.to_sexp x0; CeresS.Atom_ (CeresS.Raw ",")]) x)).
      { generalize dependent elts.
        induction x; intros elts H H1;
          cbn in H1; inv H1; auto.

        repeat break_match_hyp_inv.
        cbn.
        erewrite H; eauto.
        2: repeat constructor.

        rewrite IHx; eauto.

        intros u H0 dv_inf H1.
        eapply H; eauto.
        clear - H0.
        dependent induction H0.
        - inv H.
          constructor.
          constructor.
          right; auto.
        - specialize (IHclos_trans2 t _ eq_refl).
          eapply t_trans.
          apply H0_.
          apply IHclos_trans2.        
      }

      rewrite H0.
      reflexivity.
    - (* Vectors *)
      cbn.
      assert ((map
         (fun x0 : E2.DV.dvalue =>
            CeresS.List [CeresSerialize.to_sexp x0; CeresS.Atom_ (CeresS.Raw ",")]) elts) =
                (map
         (fun x0 : E1.DV.dvalue =>
            CeresS.List [CeresSerialize.to_sexp x0; CeresS.Atom_ (CeresS.Raw ",")]) x)).
      { generalize dependent elts.
        induction x; intros elts H H1;
          cbn in H1; inv H1; auto.

        repeat break_match_hyp_inv.
        cbn.
        erewrite H; eauto.
        2: repeat constructor.

        rewrite IHx; eauto.

        intros u H0 dv_inf H1.
        eapply H; eauto.
        clear - H0.
        dependent induction H0.
        - inv H.
          constructor.
          constructor.
          right; auto.
        - specialize (IHclos_trans2 t _ eq_refl).
          eapply t_trans.
          apply H0_.
          apply IHclos_trans2.        
      }

      rewrite H0.
      reflexivity.
  Qed.

  Lemma ceres_to_string_fin_inf :
    forall dv_fin dv_inf,
      dvalue_refine_strict dv_inf dv_fin ->
      CeresSerialize.to_string dv_fin = CeresSerialize.to_string dv_inf.
  Proof.
    intros dv_fin dv_inf REF.
    unfold CeresSerialize.to_string.
    erewrite ceres_to_sexp_fin_inf; eauto.
  Qed.

  (* TODO: Move this / generalize monad? *)
  Lemma eval_fop_err_fin_inf :
    forall dv1_fin dv2_fin err_msg fop dv1_inf dv2_inf,
      @eval_fop err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        fop dv1_fin dv2_fin = ERR_unERR_UB_OOM err_msg ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @IS1.LP.Events.DV.eval_fop err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        fop dv1_inf dv2_inf = ERR_unERR_UB_OOM err_msg.
  Proof.
    intros dv1_fin dv2_fin err_msg fop dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    unfold eval_fop in EVAL.
    (* Nasty case analysis... *)
    break_match_hyp_inv;
      repeat rewrite_fin_to_inf_dvalue;
      repeat erewrite ceres_to_string_fin_inf;
      try apply fin_to_inf_dvalue_refine_strict;
      repeat rewrite_fin_to_inf_dvalue;
      cbn; eauto.

    { (* dv1: Double *)
      break_match_hyp_inv;
        repeat rewrite_fin_to_inf_dvalue;
        repeat erewrite ceres_to_string_fin_inf;
        try apply fin_to_inf_dvalue_refine_strict;
        repeat rewrite_fin_to_inf_dvalue;
        cbn; eauto.
      2: break_match_hyp_inv.

      eapply double_op_err_fin_inf; eauto.
    }

    { (* dv1: Float *)
      break_match_hyp_inv;
        repeat rewrite_fin_to_inf_dvalue;
        repeat erewrite ceres_to_string_fin_inf;
        try apply fin_to_inf_dvalue_refine_strict;
        repeat rewrite_fin_to_inf_dvalue;
        cbn; eauto.
      2: break_match_hyp_inv.

      eapply float_op_err_fin_inf; eauto.
    }
  Qed.

  (* TODO: Move this / generalize monad? *)
  Lemma eval_fcmp_ub_fin_inf :
    forall dv1_fin dv2_fin ub_msg fcmp dv1_inf dv2_inf,
      @eval_fcmp err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        fcmp dv1_fin dv2_fin = UB_unERR_UB_OOM ub_msg ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @IS1.LP.Events.DV.eval_fcmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        fcmp dv1_inf dv2_inf = UB_unERR_UB_OOM ub_msg.
  Proof.
    intros dv1_fin dv2_fin ub_msg fcmp dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    unfold eval_fcmp in EVAL.
    repeat break_match_hyp_inv.
  Qed.

  (* TODO: Move this / generalize monad? *)
  Lemma eval_fcmp_err_fin_inf :
    forall dv1_fin dv2_fin err_msg fcmp dv1_inf dv2_inf,
      @eval_fcmp err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        fcmp dv1_fin dv2_fin = ERR_unERR_UB_OOM err_msg ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      @IS1.LP.Events.DV.eval_fcmp err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        fcmp dv1_inf dv2_inf = ERR_unERR_UB_OOM err_msg.
  Proof.
    intros dv1_fin dv2_fin err_msg fcmp dv1_inf dv2_inf EVAL LIFT1 LIFT2.
    unfold eval_fcmp in EVAL.
    (* Nasty case analysis... *)
    repeat break_match_hyp_inv;
      repeat rewrite_fin_to_inf_dvalue;
      repeat erewrite ceres_to_string_fin_inf;
      try apply fin_to_inf_dvalue_refine_strict;
      repeat rewrite_fin_to_inf_dvalue;
      cbn; eauto.
  Qed.

  Lemma index_into_vec_dv_no_ub :
    forall t vec idx ub_msg,
      @index_into_vec_dv err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) t vec idx = UB_unERR_UB_OOM ub_msg -> False.
  Proof.
    intros t vec idx res INDEX.
    unfold index_into_vec_dv in INDEX.

    break_match_hyp_inv.
    { (* Arrays *)
      break_match_hyp_inv.
      { (* ix index *)
        repeat break_match_hyp_inv.
        - induction elts; cbn in *; inv H0.
        - clear Heqz.
          remember (Z.pos p) as z.
          clear Heqz p.
          generalize dependent z.
          induction elts; intros z CONTRA; cbn in *; inv CONTRA.
          break_match_hyp_inv.
          eapply IHelts in H1; auto.
      }
    }

    { (* Vectors *)
      break_match_hyp_inv.
      { (* ix index *)
        repeat break_match_hyp_inv.
        - induction elts; cbn in *; inv H0.
        - clear Heqz.
          remember (Z.pos p) as z.
          clear Heqz p.
          generalize dependent z.
          induction elts; intros z CONTRA; cbn in *; inv CONTRA.
          break_match_hyp_inv.
          eapply IHelts in H1; auto.
      }
    }
  Qed.

  (* TODO: Move this / generalize monad? *)
  (* TODO: Prove this *)
  Lemma insert_into_vec_dv_no_ub_fin_inf :
    forall dv1_fin dv2_fin dv3_fin ub_msg t,
      @insert_into_vec_dv err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        t dv1_fin dv2_fin dv3_fin = raise_ub ub_msg -> False.
  Proof.
    intros dv1_fin dv2_fin dv3_fin ub_msg t INSERT.
    unfold insert_into_vec_dv in INSERT.
    repeat break_match_hyp_inv.
  Qed.

  Lemma eval_select_ub_fin_inf :
    forall cond uv1_fin uv2_fin uv1_inf uv2_inf ub_msg
      (IH1 : forall ub_msg,
          IS2.MEM.CP.CONC.concretize_u uv1_fin (UB_unERR_UB_OOM ub_msg) ->
          IS1.MEM.CP.CONC.concretize_u uv1_inf (UB_unERR_UB_OOM ub_msg))
      (IH2 : forall ub_msg,
          IS2.MEM.CP.CONC.concretize_u uv2_fin (UB_unERR_UB_OOM ub_msg) ->
          IS1.MEM.CP.CONC.concretize_u uv2_inf (UB_unERR_UB_OOM ub_msg)),
      uvalue_refine_strict uv1_inf uv1_fin ->
      uvalue_refine_strict uv2_inf uv2_fin ->
      @eval_select ErrUbOomProp Monad_ErrUbOomProp
        (fun (dt : dtyp) (edv : err_ub_oom dvalue) =>
           match unERR_UB_OOM edv with
           | {|
               EitherMonad.unEitherT :=
                 {|
                   EitherMonad.unEitherT :=
                     {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |}
                 |}
             |} => dvalue_has_dtyp dv dt /\ dv <> DVALUE_Poison dt
           | _ => True
           end) err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (fun (A : Type) (x ue : err_ub_oom A) => x = ue) cond uv1_fin uv2_fin (UB_unERR_UB_OOM ub_msg) ->
      @IS1.MEM.CP.CONC.eval_select ErrUbOomProp Monad_ErrUbOomProp
        (fun (dt : dtyp) (edv : err_ub_oom DVCrev.DV2.dvalue) =>
           match unERR_UB_OOM edv with
           | {|
               EitherMonad.unEitherT :=
                 {|
                   EitherMonad.unEitherT :=
                     {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |}
                 |}
             |} => E1.DV.dvalue_has_dtyp dv dt /\ dv <> E1.DV.DVALUE_Poison dt
           | _ => True
           end) err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (fun (A : Type) (x ue : err_ub_oom A) => x = ue) (fin_to_inf_dvalue cond) uv1_inf uv2_inf (UB_unERR_UB_OOM ub_msg).
  Proof.
    intros cond uv1_fin uv2_fin uv1_inf uv2_inf ub_msg IH1 IH2 REF1 REF2 EVAL.
    destruct cond.
    { unfold fin_to_inf_dvalue at 1.
      break_match_goal; clear Heqs; destruct p; clear e0;
      cbn in e; break_match_hyp_inv;
        cbn in *; subst; cbn in *; auto; inv EVAL.
    }

    { (* i1 conditional *)
      rewrite eval_select_equation in *.
      rewrite IS1.MEM.CP.CONC.eval_select_equation.
      rewrite fin_to_inf_dvalue_ix.

      break_match; try inv EVAL.
      break_match.
      - eapply IH1; eauto.
      - eapply IH2; eauto.
    }

    all: try solve
           [ unfold fin_to_inf_dvalue at 1;
             break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e;
             cbn in *; subst; cbn in *; inv EVAL; auto
           | unfold fin_to_inf_dvalue at 1;
             break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e;
             cbn in *; subst; cbn in *; reflexivity
           | unfold fin_to_inf_dvalue at 1;
             break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; break_match_hyp_inv;
             cbn in *; subst; cbn in *; auto; inv EVAL
           ].

    { (* Vector conditional *)
      rewrite eval_select_equation in *.
      rewrite IS1.MEM.CP.CONC.eval_select_equation.

      rewrite_fin_to_inf_dvalue.
      repeat red.

      repeat red in EVAL.
      destruct EVAL as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { clear H1.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        eapply IH1; eauto.
      }

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).
      split.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.
      intros a ?; subst.
      repeat red.

      destruct H1 as [[] | H1].
      specialize (H1 _ eq_refl).
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { clear H2.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        eapply IH2; eauto.
      }

      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).
      split.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.
      intros a ?; subst.

      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).

      destruct x1;
        try (rewrite <- H2 in H5; inv H5).

      destruct x3;
        try (rewrite <- H2 in H5; inv H5).
      rewrite_fin_to_inf_dvalue.

      repeat red in H2.
      repeat red.

      destruct H2 as (?&?&?&?&?).
      rewrite <- H3 in H5.
      destruct_err_ub_oom x; inv H5.
      { exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        pose proof eval_select_loop_fin_inf elts elts0 elts1 (UB_unERR_UB_OOM ub_msg) as LOOP.
        specialize (LOOP H2).
        auto.
      }

      destruct H4 as [[] | H4].
      specialize (H4 _ eq_refl).
      cbn in H4.
      rewrite <- H4 in H7; inv H7.
    }
  Qed.

  Lemma concretize_uvalue_bytes_helper_ub_fin_inf :
    forall uvs_inf uvs_fin acc_inf acc_fin ub_msg
      (IH : forall (u : DV1.uvalue),
          Exists (DV1.uvalue_subterm u) uvs_inf ->
          forall uv_fin : DV2.uvalue,
            uvalue_refine_strict u uv_fin ->
            forall ub_msg,
              IS2.MEM.CP.CONC.concretize_u uv_fin (UB_unERR_UB_OOM ub_msg) ->
              IS1.MEM.CP.CONC.concretize_u u (UB_unERR_UB_OOM ub_msg)),
      Forall2 uvalue_refine_strict uvs_inf uvs_fin ->
      concretization_map_refine acc_inf acc_fin ->
      @concretize_uvalue_bytes_helper ErrUbOomProp Monad_ErrUbOomProp
        (fun (dt : dtyp) (edv : err_ub_oom dvalue) =>
           match @unERR_UB_OOM IdentityMonad.ident dvalue edv with
           | {|
               EitherMonad.unEitherT :=
                 {|
                   EitherMonad.unEitherT :=
                     {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |}
                 |}
             |} => dvalue_has_dtyp dv dt /\ dv <> DVALUE_Poison dt
           | _ => True
           end) err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (fun (A : Type) (x ue : err_ub_oom A) => x = ue) acc_fin uvs_fin (UB_unERR_UB_OOM ub_msg) ->
      @IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalue_bytes_helper ErrUbOomProp Monad_ErrUbOomProp
        (fun (dt0 : dtyp) (edv : err_ub_oom IS1.LP.Events.DV.dvalue) =>
           match @unERR_UB_OOM IdentityMonad.ident IS1.LP.Events.DV.dvalue edv with
           | {|
               EitherMonad.unEitherT :=
                 {|
                   EitherMonad.unEitherT :=
                     {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |}
                 |}
             |} => IS1.LP.Events.DV.dvalue_has_dtyp dv dt0 /\ dv <> IS1.LP.Events.DV.DVALUE_Poison dt0
           | _ => True
           end) err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (fun (A : Type) (x ue : err_ub_oom A) => x = ue) acc_inf uvs_inf (UB_unERR_UB_OOM ub_msg).
  Proof.
    (* Will need something about acc_inf and acc_fin *)
    induction uvs_inf;
      intros uvs_fin acc_inf acc_fin ub_msg IH REF ACC_REF CONC.
    - inv REF.
      cbn in CONC; inv CONC; cbn.
    - inv REF.
      rewrite concretize_uvalue_bytes_helper_equation in CONC.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalue_bytes_helper_equation.
      destruct y; uvalue_refine_strict_inv H1; try inv CONC.
      rewrite pre_concretized_fin_inf with (uv_fin:=y) (acc_fin:=acc_fin); eauto.
      break_match_hyp_inv; repeat red.
      + (* pre-concretization exists *)
        destruct H as (?&?&?&?).
        destruct_err_ub_oom x0; inv H1.
        { exists (UB_unERR_UB_OOM ub_msg).
          exists (fun _ => UB_unERR_UB_OOM ub_msg).
          split; cbn; eauto.
        }

        destruct H2 as [[] | H2].
        specialize (H2 x2).
        forward H2; [cbn; auto|].
        rewrite <- H2 in H5.
        inv H5.
      + (* No pre-concretization exists *)
        destruct H as (?&?&?&?).
        destruct_err_ub_oom x0; inv H1.
        { exists (UB_unERR_UB_OOM ub_msg).
          exists (fun _ => UB_unERR_UB_OOM ub_msg).
          split; cbn; eauto.
          eapply IH; eauto.
          repeat constructor.
        }

        exists (ret (fin_to_inf_dvalue x2)).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        split; cbn; eauto.
        right.
        intros ? ?; subst.
        repeat red.

        destruct H2 as [[] | H2].
        specialize (H2 x2).
        forward H2; [cbn; auto|].
        cbn in H2.
        repeat red in H2.
        destruct H2 as (?&?&?&?&?).
        rewrite <- H2 in H5.
        destruct_err_ub_oom x0; inv H5.
        { exists (UB_unERR_UB_OOM ub_msg).
          exists (fun _ => UB_unERR_UB_OOM ub_msg).
          split; cbn; eauto.
          eapply IHuvs_inf; eauto.
          eapply concretize_map_refine_new_concretized_byte_fin_inf; eauto.
          eapply fin_to_inf_dvalue_refine_strict.
        }

        exists (ret (fin_to_inf_dvalue_bytes x4)).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split.
        eapply concretize_uvalue_bytes_helper_fin_inf; eauto.
        intros u H5 uv_fin H6 dv_fin H8.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        eapply concretize_map_refine_new_concretized_byte_fin_inf; eauto.
        eapply fin_to_inf_dvalue_refine_strict.

        destruct H4 as [[] | H4].
        specialize (H4 x4).
        forward H4; [cbn; auto|].
        rewrite <- H4 in H7.
        inv H7.
  Qed.

  (* Lemma concretize_uvalue_bytes_ub_fin_inf : *)
  (*   forall uvs_inf uvs_fin ub_msg *)
  (*     (IH : forall (u : DV1.uvalue), *)
  (*         Exists (DV1.uvalue_subterm u) uvs_inf -> *)
  (*         forall uv_fin : DV2.uvalue, *)
  (*           uvalue_refine_strict u uv_fin -> *)
  (*           forall ub_msg, *)
  (*             IS2.MEM.CP.CONC.concretize_u uv_fin (UB_unERR_UB_OOM ub_msg) -> *)
  (*             IS1.MEM.CP.CONC.concretize_u u (UB_unERR_UB_OOM ub_msg)), *)
  (*     Forall2 uvalue_refine_strict uvs_inf uvs_fin -> *)
  (*     @concretize_uvalue_bytes ErrUbOomProp Monad_ErrUbOomProp *)
  (*       (fun (dt : dtyp) (edv : err_ub_oom dvalue) => *)
  (*          match @unERR_UB_OOM IdentityMonad.ident dvalue edv with *)
  (*          | {| *)
  (*              EitherMonad.unEitherT := *)
  (*                {| *)
  (*                  EitherMonad.unEitherT := *)
  (*                    {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |} *)
  (*                |} *)
  (*            |} => dvalue_has_dtyp dv dt /\ dv <> DVALUE_Poison dt *)
  (*          | _ => True *)
  (*          end) err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) *)
  (*       (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) *)
  (*       (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident) *)
  (*       (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident) *)
  (*       (fun (A : Type) (x ue : err_ub_oom A) => x = ue) uvs_fin (UB_unERR_UB_OOM ub_msg) -> *)
  (*     @IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalue_bytes ErrUbOomProp Monad_ErrUbOomProp *)
  (*       (fun (dt0 : dtyp) (edv : err_ub_oom IS1.LP.Events.DV.dvalue) => *)
  (*          match @unERR_UB_OOM IdentityMonad.ident IS1.LP.Events.DV.dvalue edv with *)
  (*          | {| *)
  (*              EitherMonad.unEitherT := *)
  (*                {| *)
  (*                  EitherMonad.unEitherT := *)
  (*                    {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |} *)
  (*                |} *)
  (*            |} => IS1.LP.Events.DV.dvalue_has_dtyp dv dt0 /\ dv <> IS1.LP.Events.DV.DVALUE_Poison dt0 *)
  (*          | _ => True *)
  (*          end) err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) *)
  (*       (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) *)
  (*       (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident) *)
  (*       (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident) *)
  (*       (fun (A : Type) (x ue : err_ub_oom A) => x = ue) uvs_inf (UB_unERR_UB_OOM ub_msg). *)
  (* Proof. *)
  (*   intros uvs_inf uvs_fin ub_msg IH REF CONC. *)
  (*   rewrite concretize_uvalue_bytes_equation in CONC. *)
  (*   rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalue_bytes_equation. *)
  (*   eapply concretize_uvalue_bytes_helper_ub_fin_inf; eauto. *)
  (*   eapply concretization_map_refine_empty. *)
  (* Qed. *)

  Lemma dvalue_bytes_to_dvalue_ub_fin_inf :
    forall τ dvbs_inf dvbs_fin ub_msg,
      dvalue_bytes_refine dvbs_inf dvbs_fin ->
      @ErrOOMPoison_handle_poison_and_oom (err_ub_oom_T IdentityMonad.ident)
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident) dvalue
        DVALUE_Poison (DVALUE_BYTES.dvalue_bytes_to_dvalue dvbs_fin τ) = UB_unERR_UB_OOM ub_msg ->
      @ErrOOMPoison_handle_poison_and_oom (err_ub_oom_T IdentityMonad.ident)
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        IS1.LP.Events.DV.dvalue IS1.LP.Events.DV.DVALUE_Poison (IS1.LLVM.MEM.MP.DVALUE_BYTES.dvalue_bytes_to_dvalue dvbs_inf τ) = UB_unERR_UB_OOM ub_msg.
  Proof.
    intros τ dvbs_inf dvbs_fin ub_msg H H0.
    remember (@DVALUE_BYTES.dvalue_bytes_to_dvalue ErrOOMPoison
            (@EitherMonad.Monad_eitherT ERR_MESSAGE (OomableT Poisonable)
               (@Monad_OomableT Poisonable MonadPoisonable))
            (@RAISE_ERROR_MonadExc ErrOOMPoison
               (@EitherMonad.Exception_eitherT ERR_MESSAGE (OomableT Poisonable)
                  (@Monad_OomableT Poisonable MonadPoisonable)))
            (@RAISE_POISON_E_MT (OomableT Poisonable) (EitherMonad.eitherT ERR_MESSAGE)
               (@EitherMonad.MonadT_eitherT ERR_MESSAGE (OomableT Poisonable)
                  (@Monad_OomableT Poisonable MonadPoisonable))
               (@RAISE_POISON_E_MT Poisonable OomableT (@MonadT_OomableT Poisonable MonadPoisonable)
                  RAISE_POISON_Poisonable))
            (@RAISE_OOMABLE_E_MT (OomableT Poisonable) (EitherMonad.eitherT ERR_MESSAGE)
               (@EitherMonad.MonadT_eitherT ERR_MESSAGE (OomableT Poisonable)
                  (@Monad_OomableT Poisonable MonadPoisonable))
               (@RAISE_OOMABLE_OomableT Poisonable MonadPoisonable)) dvbs_fin τ).
    destruct e.
    destruct unEitherT.
    destruct unMkOomableT; inv H0.
    destruct o; inv H2.
    destruct s; inv H1.
    destruct e; inv H2.
  Qed.

  (* Lemma extractbytes_to_dvalue_ub_fin_inf : *)
  (*   forall uvs l ub_msg dt *)
  (*     (Heqo : map_monad uvalue_convert_strict uvs = NoOom l) *)
  (*     (IH : forall (u : DV1.uvalue), *)
  (*         Exists (DV1.uvalue_subterm u) uvs -> *)
  (*         forall uv_fin : DV2.uvalue, *)
  (*           uvalue_refine_strict u uv_fin -> *)
  (*           forall ub_msg, *)
  (*             IS2.MEM.CP.CONC.concretize_u uv_fin (UB_unERR_UB_OOM ub_msg) -> *)
  (*             IS1.MEM.CP.CONC.concretize_u u (UB_unERR_UB_OOM ub_msg)), *)
  (*     @extractbytes_to_dvalue ErrUbOomProp Monad_ErrUbOomProp *)
  (*       (fun (dt : dtyp) (edv : err_ub_oom dvalue) => *)
  (*          match @unERR_UB_OOM IdentityMonad.ident dvalue edv with *)
  (*          | {| *)
  (*              EitherMonad.unEitherT := *)
  (*                {| *)
  (*                  EitherMonad.unEitherT := *)
  (*                    {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |} *)
  (*                |} *)
  (*            |} => dvalue_has_dtyp dv dt /\ dv <> DVALUE_Poison dt *)
  (*          | _ => True *)
  (*          end) err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) *)
  (*       (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) *)
  (*       (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident) *)
  (*       (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident) *)
  (*       (fun (A : Type) (x ue : err_ub_oom A) => x = ue) l dt (UB_unERR_UB_OOM ub_msg) -> *)
  (*     @IS1.LLVM.MEM.CP.CONCBASE.extractbytes_to_dvalue ErrUbOomProp Monad_ErrUbOomProp *)
  (*       (fun (dt0 : dtyp) (edv : err_ub_oom IS1.LP.Events.DV.dvalue) => *)
  (*          match @unERR_UB_OOM IdentityMonad.ident IS1.LP.Events.DV.dvalue edv with *)
  (*          | {| *)
  (*              EitherMonad.unEitherT := *)
  (*                {| *)
  (*                  EitherMonad.unEitherT := *)
  (*                    {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |} *)
  (*                |} *)
  (*            |} => IS1.LP.Events.DV.dvalue_has_dtyp dv dt0 /\ dv <> IS1.LP.Events.DV.DVALUE_Poison dt0 *)
  (*          | _ => True *)
  (*          end) err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) *)
  (*       (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident) *)
  (*       (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident) *)
  (*       (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident) *)
  (*       (fun (A : Type) (x ue : err_ub_oom A) => x = ue) uvs dt *)
  (*       (UB_unERR_UB_OOM ub_msg). *)
  (* Proof. *)
  (*   intros uvs l ub_msg dt Heqo IH EXTRACT. *)
  (*   rewrite IS1.LLVM.MEM.CP.CONCBASE.extractbytes_to_dvalue_equation. *)
  (*   rewrite extractbytes_to_dvalue_equation in EXTRACT. *)
  (*   repeat red in EXTRACT. *)
  (*   destruct EXTRACT as (?&?&?&?&?). *)
  (*   destruct_err_ub_oom x; inv H0. *)
  (*   { exists (UB_unERR_UB_OOM ub_msg). *)
  (*     exists (fun _ => UB_unERR_UB_OOM ub_msg). *)
  (*     split; cbn; eauto. *)
  (*     eapply concretize_uvalue_bytes_ub_fin_inf; eauto. *)
  (*     eapply map_monad_oom_Forall2; eauto. *)
  (*   } *)

  (*   destruct H1 as [[] | H1]. *)
  (*   specialize (H1 x1). *)
  (*   forward H1; [cbn; auto|]. *)
  (*   remember (x0 x1) as x0x1. *)
  (*   destruct_err_ub_oom x0x1; inv H3. *)

  (*   eapply concretize_uvalue_bytes_fin_inf in H; eauto. *)
  (*   3: eapply map_monad_oom_Forall2; eauto. *)
  (*   2: { *)
  (*     intros u H0 uv_fin H2 dv_fin H3. *)
  (*     eapply uvalue_concretize_strict_concretize_inclusion; eauto. *)
  (*   } *)

  (*   exists (ret (fin_to_inf_dvalue_bytes x1)). *)
  (*   exists (fun _ => UB_unERR_UB_OOM ub_msg). *)
  (*   split; eauto. *)
  (*   split; eauto. *)
  (*   right. *)
  (*   intros a RETa. *)
  (*   inv RETa. *)
  (*   eapply dvalue_bytes_to_dvalue_ub_fin_inf; eauto. *)
  (*   apply dvalue_bytes_refine_fin_to_inf_dvalue_bytes. *)
  (* Qed. *)

  Lemma concretize_ub_fin_inf :
    forall uv_inf uv_fin ub_msg
      (REF : uvalue_refine_strict uv_inf uv_fin)
      (UB: concretize_u uv_fin (UB_unERR_UB_OOM ub_msg)),
      IS1.LLVM.MEM.CP.CONC.concretize_u uv_inf (UB_unERR_UB_OOM ub_msg).
  Proof.
    induction uv_inf using DV1.uvalue_strong_ind;
      intros uv_fin ub_msg REF UB;
      try
        solve
        [ unfold_uvalue_refine_strict;
          try inv REF;
          repeat break_match_hyp_inv;
          repeat red in UB;
          rewrite CONC.concretize_uvalueM_equation in UB; inv UB
        | cbn; auto
        ].

    destruct uv_inf;
      try
        solve
        [ unfold_uvalue_refine_strict;
          try inv REF;
          repeat break_match_hyp_inv;
          repeat red in UB;
          rewrite CONC.concretize_uvalueM_equation in UB; inv UB
        | cbn; auto
        ].

    - (* Structs *)
      unfold_uvalue_refine_strict_in REF.
      break_match_hyp_inv.
      eapply map_monad_oom_Forall2 in Heqo.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; inv H1.
      { (* UB when concretizing l *)
        clear H2.
        induction Heqo.
        - cbn in H0; inv H0.
        - rewrite map_monad_unfold in H0.
          repeat red in H0.
          destruct H0 as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H2.
          { clear H3.
            pose proof (H x).
            forward H2.
            repeat constructor.
            specialize (H2 y ub_msg H1 H0).
            rewrite map_monad_unfold.
            repeat red.
            exists (UB_unERR_UB_OOM ub_msg).
            exists (fun _ => (UB_unERR_UB_OOM ub_msg)).

            split; cbn; eauto.
            exists (UB_unERR_UB_OOM ub_msg).
            exists (fun _ => (UB_unERR_UB_OOM ub_msg)).

            split; cbn; eauto.
          }

          (* No UB on first element *)
          destruct H3 as [[] | H3].
          specialize (H3 x3).
          forward H3; [cbn; auto|].
          destruct H3 as (?&?&?&?&?).
          rewrite <- H3 in H5.
          destruct_err_ub_oom x1; inv H5.
          2: {
            destruct H4 as [[] | H4].
            specialize (H4 x5); forward H4; [cbn;auto|].

            cbn in H4.
            rewrite <- H4 in H7.
            inv H7.
          }

          repeat red.
          exists (UB_unERR_UB_OOM ub_msg).
          exists (fun _ => (UB_unERR_UB_OOM ub_msg)).
          split; cbn; eauto.

          repeat red.
          pose proof uvalue_concretize_strict_concretize_inclusion _ _ H1 as INC.
          red in INC.
          specialize (INC _ H0).

          exists (ret (fin_to_inf_dvalue x3)).
          exists (fun _ => (UB_unERR_UB_OOM ub_msg)).
          split; cbn; eauto.
          split; cbn; eauto.
          right.
          intros a H5; subst.

          repeat red.
          exists (UB_unERR_UB_OOM ub_msg).
          exists (fun _ => (UB_unERR_UB_OOM ub_msg)).
          split; cbn; eauto.

          forward IHHeqo.
          intros u H5 uv_fin ub_msg0 REF UB.
          eapply H; try right; eauto.
          { clear - H5.
            dependent induction H5.
            - inv H.
              constructor.
              constructor.
              right; auto.
            - specialize (IHclos_trans2 l eq_refl).
              eapply t_trans.
              apply H5_.
              apply IHclos_trans2.
          }

          forward IHHeqo; eauto.
          repeat red in IHHeqo.
          destruct IHHeqo as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H6; eauto.

          destruct H7 as [[] | H7].
          specialize (H7 x6); forward H7; [cbn;auto|].

          cbn in H7.
          rewrite <- H7 in H9.
          inv H9.
      }

      (* Concretizing fields succeeds, should be a contradiction *)
      destruct H2 as [[] | H2].
      specialize (H2 x1 eq_refl).
      cbn in H2.
      rewrite <- H2 in H4.
      cbn in H4. inv H4.
    - (* Packed structs *)
      unfold_uvalue_refine_strict_in REF.
      break_match_hyp_inv.
      eapply map_monad_oom_Forall2 in Heqo.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; inv H1.
      { (* UB when concretizing l *)
        clear H2.
        induction Heqo.
        - cbn in H0; inv H0.
        - rewrite map_monad_unfold in H0.
          repeat red in H0.
          destruct H0 as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H2.
          { clear H3.
            pose proof (H x).
            forward H2.
            repeat constructor.
            specialize (H2 y ub_msg H1 H0).

            rewrite map_monad_unfold.
            repeat red.
            exists (UB_unERR_UB_OOM ub_msg).
            exists (fun _ => (UB_unERR_UB_OOM ub_msg)).

            split; cbn; eauto.
            exists (UB_unERR_UB_OOM ub_msg).
            exists (fun _ => (UB_unERR_UB_OOM ub_msg)).

            split; cbn; eauto.
          }

          (* No UB on first element *)
          destruct H3 as [[] | H3].
          specialize (H3 x3).
          forward H3; [cbn; auto|].
          destruct H3 as (?&?&?&?&?).
          rewrite <- H3 in H5.
          destruct_err_ub_oom x1; inv H5.
          2: {
            destruct H4 as [[] | H4].
            specialize (H4 x5); forward H4; [cbn;auto|].

            cbn in H4.
            rewrite <- H4 in H7.
            inv H7.
          }

          repeat red.
          exists (UB_unERR_UB_OOM ub_msg).
          exists (fun _ => (UB_unERR_UB_OOM ub_msg)).
          split; cbn; eauto.

          repeat red.
          pose proof uvalue_concretize_strict_concretize_inclusion _ _ H1 as INC.
          red in INC.
          specialize (INC _ H0).

          exists (ret (fin_to_inf_dvalue x3)).
          exists (fun _ => (UB_unERR_UB_OOM ub_msg)).
          split; cbn; eauto.
          split; cbn; eauto.
          right.
          intros a H5; subst.

          repeat red.
          exists (UB_unERR_UB_OOM ub_msg).
          exists (fun _ => (UB_unERR_UB_OOM ub_msg)).
          split; cbn; eauto.

          forward IHHeqo.
          intros u H5 uv_fin ub_msg0 REF UB.
          eapply H; try right; eauto.
          { clear - H5.
            dependent induction H5.
            - inv H.
              constructor.
              constructor.
              right; auto.
            - specialize (IHclos_trans2 l eq_refl).
              eapply t_trans.
              apply H5_.
              apply IHclos_trans2.
          }

          forward IHHeqo; eauto.
          repeat red in IHHeqo.
          destruct IHHeqo as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H6; eauto.

          destruct H7 as [[] | H7].
          specialize (H7 x6); forward H7; [cbn;auto|].

          cbn in H7.
          rewrite <- H7 in H9.
          inv H9.
      }

      (* Concretizing fields succeeds, should be a contradiction *)
      destruct H2 as [[] | H2].
      specialize (H2 x1 eq_refl).
      cbn in H2.
      rewrite <- H2 in H4.
      cbn in H4. inv H4.
    - (* Arrays *)
      unfold_uvalue_refine_strict_in REF.
      break_match_hyp_inv.
      eapply map_monad_oom_Forall2 in Heqo.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; inv H1.
      { (* UB when concretizing l *)
        clear H2.
        induction Heqo.
        - cbn in H0; inv H0.
        - rewrite map_monad_unfold in H0.
          repeat red in H0.
          destruct H0 as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H2.
          { clear H3.
            pose proof (H x).
            forward H2.
            repeat constructor.
            specialize (H2 y ub_msg H1 H0).
            rewrite map_monad_unfold.
            repeat red.
            exists (UB_unERR_UB_OOM ub_msg).
            exists (fun _ => (UB_unERR_UB_OOM ub_msg)).

            split; cbn; eauto.
            exists (UB_unERR_UB_OOM ub_msg).
            exists (fun _ => (UB_unERR_UB_OOM ub_msg)).

            split; cbn; eauto.
          }

          (* No UB on first element *)
          destruct H3 as [[] | H3].
          specialize (H3 x3).
          forward H3; [cbn; auto|].
          destruct H3 as (?&?&?&?&?).
          rewrite <- H3 in H5.
          destruct_err_ub_oom x1; inv H5.
          2: {
            destruct H4 as [[] | H4].
            specialize (H4 x5); forward H4; [cbn;auto|].

            cbn in H4.
            rewrite <- H4 in H7.
            inv H7.
          }

          repeat red.
          exists (UB_unERR_UB_OOM ub_msg).
          exists (fun _ => (UB_unERR_UB_OOM ub_msg)).
          split; cbn; eauto.

          repeat red.
          pose proof uvalue_concretize_strict_concretize_inclusion _ _ H1 as INC.
          red in INC.
          specialize (INC _ H0).

          exists (ret (fin_to_inf_dvalue x3)).
          exists (fun _ => (UB_unERR_UB_OOM ub_msg)).
          split; cbn; eauto.
          split; cbn; eauto.
          right.
          intros a H5; subst.

          repeat red.
          exists (UB_unERR_UB_OOM ub_msg).
          exists (fun _ => (UB_unERR_UB_OOM ub_msg)).
          split; cbn; eauto.

          forward IHHeqo.
          intros u H5 uv_fin ub_msg0 REF UB.
          eapply H; try right; eauto.
          { clear - H5.
            dependent induction H5.
            - inv H.
              constructor.
              constructor.
              right; auto.
            - specialize (IHclos_trans2 t l eq_refl).
              eapply t_trans.
              apply H5_.
              apply IHclos_trans2.
          }
          forward IHHeqo; eauto.
          repeat red in IHHeqo.
          destruct IHHeqo as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H6; eauto.

          destruct H7 as [[] | H7].
          specialize (H7 x6); forward H7; [cbn;auto|].

          cbn in H7.
          rewrite <- H7 in H9.
          inv H9.
      }

      (* Concretizing fields succeeds, should be a contradiction *)
      destruct H2 as [[] | H2].
      specialize (H2 x1 eq_refl).
      cbn in H2.
      rewrite <- H2 in H4.
      cbn in H4. inv H4.
    - (* Vectors *)
      unfold_uvalue_refine_strict_in REF.
      break_match_hyp_inv.
      eapply map_monad_oom_Forall2 in Heqo.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; inv H1.
      { (* UB when concretizing l *)
        clear H2.
        induction Heqo.
        - cbn in H0; inv H0.
        - rewrite map_monad_unfold in H0.
          repeat red in H0.
          destruct H0 as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H2.
          { clear H3.
            pose proof (H x).
            forward H2.
            repeat constructor.
            specialize (H2 y ub_msg H1 H0).
            rewrite map_monad_unfold.
            repeat red.
            exists (UB_unERR_UB_OOM ub_msg).
            exists (fun _ => (UB_unERR_UB_OOM ub_msg)).

            split; cbn; eauto.
            exists (UB_unERR_UB_OOM ub_msg).
            exists (fun _ => (UB_unERR_UB_OOM ub_msg)).

            split; cbn; eauto.
          }

          (* No UB on first element *)
          destruct H3 as [[] | H3].
          specialize (H3 x3).
          forward H3; [cbn; auto|].
          destruct H3 as (?&?&?&?&?).
          rewrite <- H3 in H5.
          destruct_err_ub_oom x1; inv H5.
          2: {
            destruct H4 as [[] | H4].
            specialize (H4 x5); forward H4; [cbn;auto|].

            cbn in H4.
            rewrite <- H4 in H7.
            inv H7.
          }

          repeat red.
          exists (UB_unERR_UB_OOM ub_msg).
          exists (fun _ => (UB_unERR_UB_OOM ub_msg)).
          split; cbn; eauto.

          repeat red.
          pose proof uvalue_concretize_strict_concretize_inclusion _ _ H1 as INC.
          red in INC.
          specialize (INC _ H0).

          exists (ret (fin_to_inf_dvalue x3)).
          exists (fun _ => (UB_unERR_UB_OOM ub_msg)).
          split; cbn; eauto.
          split; cbn; eauto.
          right.
          intros a H5; subst.

          repeat red.
          exists (UB_unERR_UB_OOM ub_msg).
          exists (fun _ => (UB_unERR_UB_OOM ub_msg)).
          split; cbn; eauto.

          forward IHHeqo.
          intros u H5 uv_fin ub_msg0 REF UB.
          eapply H; try right; eauto.
          { clear - H5.
            dependent induction H5.
            - inv H.
              constructor.
              constructor.
              right; auto.
            - specialize (IHclos_trans2 t l eq_refl).
              eapply t_trans.
              apply H5_.
              apply IHclos_trans2.
          }
          forward IHHeqo; eauto.
          repeat red in IHHeqo.
          destruct IHHeqo as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H6; eauto.

          destruct H7 as [[] | H7].
          specialize (H7 x6); forward H7; [cbn;auto|].

          cbn in H7.
          rewrite <- H7 in H9.
          inv H9.
      }

      (* Concretizing fields succeeds, should be a contradiction *)
      destruct H2 as [[] | H2].
      specialize (H2 x1 eq_refl).
      cbn in H2.
      rewrite <- H2 in H4.
      cbn in H4. inv H4.
    - (* UVALUE_ICmp *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* UB when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No UB on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* UB in second operand *)
        eapply IH in H0; eauto.
        repeat red.
        exists (ret (fin_to_inf_dvalue x1)).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        split; eauto.
        right.
        intros a H3.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* UB in evaluating operation? *)
      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      rewrite <- H2 in H5.

      remember (eval_iop iop x1 x3) as res.
      destruct_err_ub_oom res; inv H5.

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      eapply eval_iop_ub_fin_inf; eauto.
    - (* UVALUE_ICmp *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* UB when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No UB on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* UB in second operand *)
        eapply IH in H0; eauto.
        repeat red.
        exists (ret (fin_to_inf_dvalue x1)).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        split; eauto.
        right.
        intros a H3.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* UB in evaluating operation? *)
      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      rewrite <- H2 in H5.

      remember (eval_icmp cmp x1 x3) as res.
      destruct_err_ub_oom res; inv H5.

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      eapply eval_icmp_ub_fin_inf; eauto.
    - (* UVALUE_FBinop *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* UB when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No UB on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* UB in second operand *)
        eapply IH in H0; eauto.
        repeat red.
        exists (ret (fin_to_inf_dvalue x1)).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        split; eauto.
        right.
        intros a H3.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* UB in evaluating operation? *)
      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      rewrite <- H2 in H5.

      remember (eval_fop fop x1 x3) as res.
      destruct_err_ub_oom res; inv H5.

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      eapply eval_fop_ub_fin_inf; eauto.
    - (* UVALUE_FCmp *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* UB when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No UB on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* UB in second operand *)
        eapply IH in H0; eauto.
        repeat red.
        exists (ret (fin_to_inf_dvalue x1)).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        split; eauto.
        right.
        intros a H3.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* UB in evaluating operation? *)
      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      rewrite <- H2 in H5.

      remember (eval_fcmp cmp x1 x3) as res.
      destruct_err_ub_oom res; inv H5.

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      eapply eval_fcmp_ub_fin_inf; eauto.
    - (* UVALUE_Conversion *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* UB when concretizing uv *)
        eapply IH in H; eauto.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No UB on concretizing uv. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).
      split.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.
      intros a H0; subst.
      break_match_hyp.

      { (* Pure *)
        cbn in H1.
        rewrite <- H1 in H3; inv H3.
      }

      { (* ItoP *)
        break_match_hyp;
        cbn in H1;
        rewrite <- H1 in H3; inv H3.
      }

      { (* PtoI *)
        exfalso.
        repeat break_match_hyp;
        cbn in H1;
          rewrite <- H1 in H3; inv H3.
        repeat break_match_hyp_inv.
        repeat break_match_hyp_inv.
        unfold lift_OOM in Heqe.
        repeat break_match_hyp_inv; inv Heqs.
      }

      { (* Oom *)
        rewrite <- H1 in H3; inv H3.
      }

      { (* Illegal *)
        rewrite <- H1 in H3; inv H3.
      }
    - (* UVALUE_GetElementPtr *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* UB when concretizing base address *)
        eapply IH in H; eauto.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No UB on base address. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).
      split; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.
      intros a ?; subst.
      repeat red.

      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* UB in concretization of indices *)
        generalize dependent l.
        induction idxs; intros l H3 Heqo0.
        - inv Heqo0. cbn in H3. inv H3.
        - forward IHidxs.
          { intros idx H4 uv_fin ub_msg0 REF UB.
            eapply IH; eauto.
            { clear - H4.
              dependent induction H4.
              - inv H.
                constructor.
                constructor.
                constructor.
                constructor.
                right; auto.
              - specialize (IHclos_trans2 _ _ _ eq_refl).
                eapply t_trans.
                apply H4_.
                apply IHclos_trans2.
            }
          }
          rewrite map_monad_unfold in Heqo0.
          cbn in Heqo0.
          repeat break_match_hyp_inv.
          rewrite map_monad_unfold in H3.
          cbn in H3.
          repeat red in H3.
          destruct H3 as (?&?&?&?&?).
          destruct_err_ub_oom x; inv H3.
          + (* UB in first index *)
            exists (UB_unERR_UB_OOM ub_msg).
            exists (fun _ => UB_unERR_UB_OOM ub_msg).
            split.
            * rewrite map_monad_unfold.
              cbn.
              exists (UB_unERR_UB_OOM ub_msg).
              exists (fun _ => UB_unERR_UB_OOM ub_msg).
              split.
              eapply IH; cbn; eauto.
              repeat constructor.
              split; cbn; eauto.
            * split; cbn; eauto.
          + (* No UB on first index *)
            destruct H4 as [[] | H4].
            specialize (H4 x4).
            forward H4; [cbn; auto|].
            repeat red in H4.
            destruct H4 as (?&?&?&?&?).
            rewrite <- H4 in H6.

            rewrite map_monad_unfold.
            exists (UB_unERR_UB_OOM ub_msg).
            exists (fun _ => UB_unERR_UB_OOM ub_msg).
            split; cbn; eauto.

            exists (ret (fin_to_inf_dvalue x4)).
            exists (fun _ => UB_unERR_UB_OOM ub_msg).
            split; cbn; eauto.
            eapply uvalue_concretize_strict_concretize_inclusion; eauto.
            split; cbn; eauto.
            right.
            intros a0 H8; subst.
            destruct_err_ub_oom x; inv H6.
            * (* UB in map *)
              specialize (IHidxs l0 H3 eq_refl).
              destruct IHidxs as (?&?&?&?&?).
              destruct_err_ub_oom x; inv H7.
              { exists (UB_unERR_UB_OOM ub_msg).
                exists (fun _ => UB_unERR_UB_OOM ub_msg).
                split; cbn; eauto.
              }
              destruct H8 as [[] | H8].
              specialize (H8 x7).
              forward H8; [cbn; auto|].
              destruct (IS1.LLVM.MEM.MP.GEP.handle_gep t (fin_to_inf_dvalue x1) x7);
                try rewrite <- H8 in H10; try inv H10.
              destruct o;
                rewrite <- H8 in H9; inv H9.
            * destruct H5 as [[] | H5].
              specialize (H5 x6).
              forward H5; [cbn; auto|].
              rewrite <- H5 in H8.
              inv H8.
      }

      (* No UB when concretizing indices... *)
      exfalso.
      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      repeat break_match_hyp;
        rewrite <- H2 in H5; inv H5.
    - (* UVALUE_ExtractElement *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* UB when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No UB on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* UB in second operand *)
        eapply IH in H0; eauto.
        repeat red.
        exists (ret (fin_to_inf_dvalue x1)).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        split; eauto.
        right.
        intros a H3.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* UB in evaluating operation? *)
      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      repeat red in H2.
      destruct H2 as (?&?&?&?&?).
      rewrite <- H3 in H5.
      destruct vec_typ; inv H2; inv H5.

      destruct H4 as [[] | H4].
      specialize (H4 vec_typ).
      forward H4; [cbn; auto|].
      remember (index_into_vec_dv vec_typ x1 x3) as res.
      rewrite <- H4 in H6.
      destruct_err_ub_oom res; inv H6.
      symmetry in Heqres.
      eapply index_into_vec_dv_no_ub in Heqres; contradiction.
    - (* UVALUE_InsertElement *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* UB when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).
      split; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a H0.
      inv H0.

      (* No UB on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* UB uv_inf3 *)
        eapply IH in H0; eauto.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No UB on uv_inf3 *)
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).
      split; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a ?.
      inv H3.

      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      repeat red in H2.
      destruct H2 as (?&?&?&?&?).
      rewrite <- H3 in H5.
      destruct_err_ub_oom x; inv H5.

      { (* UB in uv_inf2 *)
        eapply IH in H2; eauto.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No UB on uv_inf2 *)
      exists (ret (fin_to_inf_dvalue x5)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).
      split; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a ?.
      inv H5.

      (* UB in evaluating... *)
      destruct H4 as [[] | H4].
      specialize (H4 x5).
      forward H4; [cbn; auto|].
      rewrite <- H4 in H7.
      remember (insert_into_vec_dv vec_typ x1 x5 x3) as res.
      destruct_err_ub_oom res; inv H7.
      symmetry in Heqres.
      eapply insert_into_vec_dv_no_ub_fin_inf in Heqres; contradiction.
    - (* UVALUE_ExtractValue *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* UB when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).
      split; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a H0.
      inv H0.

      (* No UB on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      rewrite <- H1 in H3.
      remember (((fix loop (str : dvalue) (idxs : list LLVMAst.int_ast) {struct idxs} :
                        err_ub_oom dvalue :=
                      match idxs with
                      | [] => ret str
                      | i :: tl => v <- index_into_str_dv str i;; loop v tl
                      end) x1 idxs)) as res.
      destruct_err_ub_oom res; inv H3.
      (* Here's should be a contradiction --- no way to get UB *)
      clear - Heqres.
      symmetry in Heqres.
      exfalso.

      generalize dependent x1.
      induction idxs; intros x1 CONTRA.
      + inv CONTRA.
      + remember (index_into_str_dv x1 a) as init.
        remember (fix loop (str : dvalue) (idxs : list LLVMAst.int_ast) {struct idxs} : err_ub_oom dvalue :=
                    match idxs with
                    | [] => ret str
                    | i :: tl => v0 <- index_into_str_dv str i;; loop v0 tl
                    end) as loop.
        clear Heqloop.

        destruct_err_ub_oom init; try solve [inv CONTRA].
        * (* UB in index_into_str_dv *)
          eapply index_into_str_dv_no_ub_fin_inf; eauto.
        * cbn in CONTRA.
          remember (loop init0 idxs) as res.
          destruct_err_ub_oom res; inv CONTRA.
          eapply IHidxs; eauto.
    - (* UVALUE_InsertValue *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* UB when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No UB on first operand. *)
      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).
      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a ?; subst.
      repeat red.

      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* UB in second operand *)
        eapply IH in H0; eauto.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No UB on second operand. *)
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).
      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a ?; subst.
      repeat red.


      (* UB in evaluating operation? *)
      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      repeat red in H2.

      pose proof H2 as LOOP.
      apply insert_value_loop_fin_inf_succeeds in LOOP.
      cbn in LOOP.
      rewrite LOOP.
      remember (x2 x3) as res.
      destruct_err_ub_oom res; inv H5.
      reflexivity.
    - (* UVALUE_Select *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* UB when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).
      split; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a H0.
      inv H0.

      (* No UB on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      remember (x0 x1) as res.
      destruct_err_ub_oom res; inv H3; eauto.

      epose proof eval_select_ub_fin_inf x1 u0 u1 uv_inf2 uv_inf3 _ as EVAL.
      forward EVAL; [intros ? ?; eapply IH; eauto; repeat constructor|].
      forward EVAL; [intros ? ?; eapply IH; eauto; repeat constructor|].
      forward EVAL; eauto.
      forward EVAL; eauto.
      forward EVAL.
      { rewrite eval_select_equation.
        eauto.
      }

      rewrite IS1.MEM.CP.CONC.eval_select_equation in EVAL.
      auto.
    - (* UVALUE_ConcatBytes *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in UB.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in UB.

      erewrite map_monad_oom_length; eauto.
      erewrite sizeof_dtyp_fin_inf; eauto.
      erewrite all_extract_bytes_from_uvalue_fin_inf; eauto.
      break_match_hyp.
      2: {
        cbn.
        cbn in UB.
        repeat red in UB.
        destruct UB as (?&?&?&?&?).
        destruct_err_ub_oom x; inv H0.
        { exists (UB_unERR_UB_OOM ub_msg).
          exists (fun _ => UB_unERR_UB_OOM ub_msg).
          split; cbn; eauto.
          eapply concretize_uvalue_bytes_helper_ub_fin_inf; eauto.
          2: eapply map_monad_oom_Forall2; eauto.
          2: apply concretization_map_refine_empty.

          intros u H0 uv_fin H2 ub_msg0 H3.
          eapply IH; eauto.
          eapply IS1.LP.Events.DV.uvalue_concat_bytes_strict_subterm; eauto.
        }

        destruct H1 as [[] | H1].
        specialize (H1 x1).
        forward H1; [cbn; auto|].
        remember (x0 x1) as x0x1.
        destruct_err_ub_oom x0x1; inv H3.

        eapply concretize_uvalue_bytes_helper_fin_inf in H; eauto.
        3: eapply map_monad_oom_Forall2; eauto.
        2: {
          intros u H0 uv_fin H2 dv_fin H3.
          eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        }

        exists (ret (fin_to_inf_dvalue_bytes x1)).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; eauto.
        split; eauto.
        right.
        intros a RETa.
        inv RETa.
        eapply dvalue_bytes_to_dvalue_ub_fin_inf; eauto.
        apply dvalue_bytes_refine_fin_to_inf_dvalue_bytes.
        apply concretization_map_refine_empty.
      }
      pose proof (map_monad_oom_length _ _ _ Heqo) as LEN.

      break_match_hyp.
      { (* UB when concretizing first operand *)
        destruct uvs.
        { inv Heqo.
          cbn in Heqo0; inv Heqo0.
        }
        rewrite map_monad_unfold in Heqo.
        cbn in Heqo.
        repeat break_match_hyp_inv.
        destruct u1; inv Heqo0.
        repeat break_match_hyp_inv.
        unfold OptionUtil.guard_opt in *.
        repeat break_match_hyp_inv.
        apply dtyp_eqb_eq in Heqb4; subst.
        rewrite H1; cbn.

        uvalue_convert_strict_inv Heqo1.
        eapply IH; eauto.
        eapply IS1.LP.Events.DV.uvalue_concat_bytes_strict_subterm; eauto.
        repeat constructor.
      }

      cbn.
      cbn in UB.
      repeat red in UB.
      destruct UB as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { exists (UB_unERR_UB_OOM ub_msg).
        exists (fun _ => UB_unERR_UB_OOM ub_msg).
        split; cbn; eauto.
        eapply concretize_uvalue_bytes_helper_ub_fin_inf; eauto.
        2: eapply map_monad_oom_Forall2; eauto.
        2: eapply concretization_map_refine_empty.

        intros u H0 uv_fin H2 ub_msg0 H3.
        eapply IH; eauto.
        eapply DV1.uvalue_concat_bytes_strict_subterm; auto.
      }

      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      remember (x0 x1) as x0x1.
      destruct_err_ub_oom x0x1; inv H3.

      eapply concretize_uvalue_bytes_helper_fin_inf in H; eauto.
      3: eapply map_monad_oom_Forall2; eauto.
      2: {
        intros u H0 uv_fin H2 dv_fin H3.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      }

      exists (ret (fin_to_inf_dvalue_bytes x1)).
      exists (fun _ => UB_unERR_UB_OOM ub_msg).
      split; eauto.
      split; eauto.
      right.
      intros a RETa.
      inv RETa.
      eapply dvalue_bytes_to_dvalue_ub_fin_inf; eauto.
      apply dvalue_bytes_refine_fin_to_inf_dvalue_bytes.

      apply concretization_map_refine_empty.
  Qed.

  Lemma concretize_no_ub_inf_fin :
    forall uv_inf uv_fin
      (REF : uvalue_refine_strict uv_inf uv_fin)
      (UB : forall ub_msg : string, ~ IS1.LLVM.MEM.CP.CONC.concretize_u uv_inf (UB_unERR_UB_OOM ub_msg)),
    forall ub_msg : string, ~ concretize_u uv_fin (UB_unERR_UB_OOM ub_msg).
  Proof.
    intros uv_inf uv_fin REF UB ub_msg.
    intros CONC.
    eapply UB;
      eapply concretize_ub_fin_inf; eauto.
  Qed.

  Lemma dvalue_bytes_to_dvalue_err_fin_inf :
    forall τ dvbs_inf dvbs_fin err_msg,
      dvalue_bytes_refine dvbs_inf dvbs_fin ->
      @ErrOOMPoison_handle_poison_and_oom (err_ub_oom_T IdentityMonad.ident)
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident) dvalue
        DVALUE_Poison (DVALUE_BYTES.dvalue_bytes_to_dvalue dvbs_fin τ) = ERR_unERR_UB_OOM err_msg ->
      @ErrOOMPoison_handle_poison_and_oom (err_ub_oom_T IdentityMonad.ident)
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        IS1.LP.Events.DV.dvalue IS1.LP.Events.DV.DVALUE_Poison (IS1.LLVM.MEM.MP.DVALUE_BYTES.dvalue_bytes_to_dvalue dvbs_inf τ) = ERR_unERR_UB_OOM err_msg.
  Proof.
    intros τ dvbs_inf dvbs_fin err_msg H H0.
    remember (@DVALUE_BYTES.dvalue_bytes_to_dvalue ErrOOMPoison
                (@EitherMonad.Monad_eitherT ERR_MESSAGE (OomableT Poisonable)
                   (@Monad_OomableT Poisonable MonadPoisonable))
                (@RAISE_ERROR_MonadExc ErrOOMPoison
                   (@EitherMonad.Exception_eitherT ERR_MESSAGE (OomableT Poisonable)
                      (@Monad_OomableT Poisonable MonadPoisonable)))
                (@RAISE_POISON_E_MT (OomableT Poisonable) (EitherMonad.eitherT ERR_MESSAGE)
                   (@EitherMonad.MonadT_eitherT ERR_MESSAGE (OomableT Poisonable)
                      (@Monad_OomableT Poisonable MonadPoisonable))
                   (@RAISE_POISON_E_MT Poisonable OomableT (@MonadT_OomableT Poisonable MonadPoisonable)
                      RAISE_POISON_Poisonable))
                (@RAISE_OOMABLE_E_MT (OomableT Poisonable) (EitherMonad.eitherT ERR_MESSAGE)
                   (@EitherMonad.MonadT_eitherT ERR_MESSAGE (OomableT Poisonable)
                      (@Monad_OomableT Poisonable MonadPoisonable))
                   (@RAISE_OOMABLE_OomableT Poisonable MonadPoisonable)) dvbs_fin τ).
    destruct_err_oom_poison e; inv H0.
    cbn in *.
    break_match_hyp_inv.
    erewrite dvalue_bytes_fin_to_dvalue_fin_inf; cbn; eauto.
    rewrite <- Heqe; cbn.
    reflexivity.

    intros x CONTRA.
    rewrite CONTRA in Heqe.
    inv Heqe.
  Qed.

  Lemma get_conv_case_bitcast_illegal_fin_inf :
    forall (t_from : dtyp)
      (dv : dvalue)
      (t_to : dtyp)
      (msg : string)
      (CONV : get_conv_case LLVMAst.Bitcast t_from dv t_to = Conv_Illegal msg),
      IS1.LLVM.MEM.CP.CONC.get_conv_case LLVMAst.Bitcast t_from (fin_to_inf_dvalue dv) t_to =
        IS1.LP.Events.DV.Conv_Illegal msg.
  Proof.
    intros t_from dv t_to msg CONV.
    cbn in *; inv CONV; auto.

    unfold MemHelpers.dtyp_eqb,
      IS1.LLVM.MEM.CP.CONC.MemHelpers.dtyp_eqb in *.
    break_match_hyp_inv.
    setoid_rewrite bit_sizeof_dtyp_fin_inf.
    break_match_hyp_inv; auto.
    remember (ErrOOMPoison_handle_poison_and_oom DVALUE_Poison
                          (DVALUE_BYTES.dvalue_bytes_to_dvalue
                             (DVALUE_BYTES.dvalue_to_dvalue_bytes dv t_from) t_to)) as res.
    destruct_err_ub_oom res; inv H0; cbn in *.
    { erewrite dvalue_bytes_to_dvalue_ub_fin_inf; eauto.
      cbn. auto.
      rewrite dvalue_to_dvalue_bytes_fin_to_inf_dvalue.
      apply dvalue_bytes_refine_fin_to_inf_dvalue_bytes.
    }

    { erewrite dvalue_bytes_to_dvalue_err_fin_inf; cbn; eauto.
      rewrite dvalue_to_dvalue_bytes_fin_to_inf_dvalue.
      apply dvalue_bytes_refine_fin_to_inf_dvalue_bytes.
    }
  Qed.

  (* TODO: Move this *)
  Lemma get_conv_case_illegal_fin_inf:
    forall conv t_from dv t_to msg,
      get_conv_case conv t_from dv t_to = Conv_Illegal msg ->
      IS1.LLVM.MEM.CP.CONC.get_conv_case conv t_from (fin_to_inf_dvalue dv) t_to = IS1.LP.Events.DV.Conv_Illegal msg.
  Proof.
    intros conv t_from dv t_to msg CONV.
    destruct conv;
      try solve
        [ cbn in *;
          try inv CONV; try reflexivity;
          repeat break_match_hyp_inv;
          auto;
          rewrite_fin_to_inf_dvalue;
          auto;
          try rewrite Heqb; auto
        ].
    - apply get_conv_case_bitcast_illegal_fin_inf; auto.
  Qed.

  Lemma handle_gep_h_err_fin_inf :
    forall  idxs_fin idxs_inf t base msg,
      GEP.handle_gep_h t base idxs_fin = inl msg ->
      map fin_to_inf_dvalue idxs_fin = idxs_inf ->
      IS1.LLVM.MEM.MP.GEP.handle_gep_h t base idxs_inf = inl msg.
  Proof.
    induction idxs_fin;
      intros idxs_inf t base msg GEP IDXS.
    - cbn in *; subst; cbn in *; auto.
    - cbn in *.
      (* Split based on index type *)
      break_match_hyp_inv;
        cbn;
        rewrite_fin_to_inf_dvalue;
        auto.

      all: rewrite H0.

      all:
        try solve [break_match_hyp_inv; auto;
                   erewrite IHidxs_fin; eauto;
                   repeat rewrite sizeof_dtyp_fin_inf;
                   repeat rewrite dtyp_alignment_fin_inf;
                   repeat rewrite padded_fin_inf;
                   eauto
          ].

      + break_match_hyp_inv; auto.
        try solve [erewrite IHidxs_fin; eauto;
                   repeat setoid_rewrite sizeof_dtyp_fin_inf;
                   repeat setoid_rewrite dtyp_alignment_fin_inf;
                   repeat setoid_rewrite padding_fin_inf; eauto
                  | break_match_hyp_inv; auto;
                    erewrite IHidxs_fin; eauto;
                    replace (fun (acc : Z) (t : dtyp) => (pad_to_align (IS1.LP.SIZEOF.dtyp_alignment t) acc + IS1.LP.SIZEOF.sizeof_dtyp t))%Z with
                      (fun (acc : Z) (t : dtyp) => (pad_to_align (SIZEOF.dtyp_alignment t) acc + SIZEOF.sizeof_dtyp t)%Z); eauto;
                    apply FunctionalExtensionality.functional_extensionality;
                    intros;
                    apply FunctionalExtensionality.functional_extensionality;
                    intros;
                    repeat setoid_rewrite sizeof_dtyp_fin_inf;
                    repeat setoid_rewrite padding_fin_inf;
                    auto

            ].

        repeat break_match_hyp_inv;
          try rewrite H1;
          try rewrite H0;
          repeat setoid_rewrite sizeof_dtyp_fin_inf;
          repeat setoid_rewrite dtyp_alignment_fin_inf;
          repeat setoid_rewrite padding_fin_inf;
          eauto.

        replace
          (fun (acc : N) (t : dtyp) =>
             pad_to_align (IS1.LP.SIZEOF.dtyp_alignment t) acc + IS1.LP.SIZEOF.sizeof_dtyp t) with
          (fun (acc : N) (t : dtyp) =>
             pad_to_align (SIZEOF.dtyp_alignment t) acc + SIZEOF.sizeof_dtyp t); eauto;
          apply FunctionalExtensionality.functional_extensionality;
          intros;
          apply FunctionalExtensionality.functional_extensionality;
          intros;
          repeat setoid_rewrite sizeof_dtyp_fin_inf;
          repeat setoid_rewrite dtyp_alignment_fin_inf;
          repeat setoid_rewrite padding_fin_inf;
          auto.

        replace
          (fun (acc : N) (t : dtyp) =>
             acc + IS1.LP.SIZEOF.sizeof_dtyp t) with
          (fun (acc : N) (t : dtyp) =>
             acc + SIZEOF.sizeof_dtyp t); eauto;
          apply FunctionalExtensionality.functional_extensionality;
          intros;
          apply FunctionalExtensionality.functional_extensionality;
          intros;
          repeat setoid_rewrite sizeof_dtyp_fin_inf;
          repeat setoid_rewrite dtyp_alignment_fin_inf;
          repeat setoid_rewrite padding_fin_inf;
          auto.

      + break_match_hyp_inv; eauto;
          repeat setoid_rewrite sizeof_dtyp_fin_inf;
          repeat setoid_rewrite dtyp_alignment_fin_inf;
          repeat setoid_rewrite padding_fin_inf;
          rewrite H1;
          erewrite IHidxs_fin;
          eauto.

        unfold intptr_fin_inf; break_inner_match_goal; clear Heqs.
        rewrite <- (IS1.LP.IP.from_Z_injective _ _ _ e (IS1.LP.IP.to_Z_from_Z x0)).
        eauto.

        unfold intptr_fin_inf; break_inner_match_goal; clear Heqs.
        rewrite <- (IS1.LP.IP.from_Z_injective _ _ _ e (IS1.LP.IP.to_Z_from_Z x0)).
        eauto.
  Qed.

  Lemma handle_gep_addr_err_fin_inf :
    forall t base_addr_fin base_addr_inf idxs_fin idxs_inf msg,
      GEP.handle_gep_addr t base_addr_fin idxs_fin = inl msg ->
      map fin_to_inf_dvalue idxs_fin = idxs_inf ->
      AC2.addr_convert base_addr_fin = NoOom base_addr_inf ->
      IS1.LLVM.MEM.MP.GEP.handle_gep_addr t base_addr_inf idxs_inf = inl msg.
  Proof.
    intros t base_addr_fin base_addr_inf
      idxs_fin idxs_inf
      msg GEP IDXS BASE_ADDR.

    destruct idxs_fin; cbn in *; subst; inv GEP; auto.
    destruct d; rewrite_fin_to_inf_dvalue; cbn in *; inv H0; auto.
    { repeat break_match_goal; try solve [try inv H0; try inv H1; auto];
        break_match_hyp_inv;
        erewrite handle_gep_h_err_fin_inf in Heqs;
          erewrite AC2.addr_convert_ptoi in Heqs0; eauto;
          try rewrite sizeof_dtyp_fin_inf; eauto;
          inv Heqs; auto.
    }

    { repeat break_match_goal; try solve [try inv H0; try inv H1; auto];
        break_match_hyp_inv;
        erewrite handle_gep_h_err_fin_inf in Heqs;
          erewrite AC2.addr_convert_ptoi in Heqs0; eauto;
          try rewrite sizeof_dtyp_fin_inf; eauto;
          inv Heqs; auto.

      unfold intptr_fin_inf; break_inner_match_goal; clear Heqs1.
      rewrite <- (IS1.LP.IP.from_Z_injective _ _ _ e (IS1.LP.IP.to_Z_from_Z x0)).
      eauto.

      unfold intptr_fin_inf; break_inner_match_goal; clear Heqs.
      rewrite <- (IS1.LP.IP.from_Z_injective _ _ _ e (IS1.LP.IP.to_Z_from_Z x0)).
      eauto.
    }
  Qed.

  Lemma index_into_vec_dv_err_fin_inf:
    forall (t : dtyp) (vec idx : dvalue) err_msg,
      index_into_vec_dv t vec idx = ERR_unERR_UB_OOM err_msg ->
      IS1.LP.Events.DV.index_into_vec_dv t (fin_to_inf_dvalue vec) (fin_to_inf_dvalue idx) = ERR_unERR_UB_OOM err_msg.
  Proof.
    intros t vec idx err_msg INDEX.
    unfold index_into_vec_dv in INDEX.
    unfold IS1.LP.Events.DV.index_into_vec_dv.

    break_match_hyp_inv; rewrite_fin_to_inf_dvalue; auto.
    { (* Arrays *)
      break_match_hyp_inv; rewrite_fin_to_inf_dvalue; auto.
      { (* ix index *)
        cbn in *.
        break_match_hyp_inv; auto.
        - remember (0%Z) as n.
          clear Heqn Heqz.
          generalize dependent n.
          induction elts; intros n H0.
          + inv H0.
          + rewrite Z.eqb_refl in H0. inv H0.
        - remember (Z.pos p) as n.
          clear Heqn Heqz.
          generalize dependent n.
          induction elts; intros n H0.
          + inv H0.
          + cbn.
            break_match_hyp_inv.
            rewrite IHelts; eauto.
      }
    }

    { (* Vectors *)
      break_match_hyp_inv; rewrite_fin_to_inf_dvalue; auto.
      { (* ix index *)
        cbn in *.
        break_match_hyp_inv; auto.
        - remember (0%Z) as n.
          clear Heqn Heqz.
          generalize dependent n.
          induction elts; intros n H0.
          + inv H0.
          + rewrite Z.eqb_refl in H0. inv H0.
        - remember (Z.pos p) as n.
          clear Heqn Heqz.
          generalize dependent n.
          induction elts; intros n H0.
          + inv H0.
          + cbn.
            break_match_hyp_inv.
            rewrite IHelts; eauto.
      }
    }
  Qed.

  Lemma insert_into_vec_dv_err_fin_inf :
    forall dv1_fin dv2_fin dv3_fin msg dv1_inf dv2_inf dv3_inf t,
      @insert_into_vec_dv err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        t dv1_fin dv2_fin dv3_fin = ERR_unERR_UB_OOM msg ->
      fin_to_inf_dvalue dv1_fin = dv1_inf ->
      fin_to_inf_dvalue dv2_fin = dv2_inf ->
      fin_to_inf_dvalue dv3_fin = dv3_inf ->
      @IS1.LP.Events.DV.insert_into_vec_dv err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        t dv1_inf dv2_inf dv3_inf = ERR_unERR_UB_OOM msg.
  Proof.
    intros dv1_fin dv2_fin dv3_fin msg dv1_inf dv2_inf dv3_inf t INSERT LIFT1 LIFT2 LIFT3.
    subst.
    unfold insert_into_vec_dv in INSERT.
    unfold IS1.LP.Events.DV.insert_into_vec_dv.

    break_match_hyp_inv; rewrite_fin_to_inf_dvalue; auto.
    { (* Arrays *)
      break_match_hyp_inv; rewrite_fin_to_inf_dvalue; auto; cbn.
      { (* ix index *)
        cbn in *.
        break_match_hyp_inv; auto.
        - remember (0%Z) as n.
          clear Heqn Heqz.
          generalize dependent n.
          induction elts; intros n H0.
          + inv H0.
          + rewrite Z.eqb_refl in H0. inv H0.
        - remember (Z.pos p) as n.
          clear Heqn Heqz.
          generalize dependent n.
          induction elts; intros n H0.
          + inv H0.
          + cbn.
            break_match_hyp_inv.
      }
    }

    { (* Vectors *)
      break_match_hyp_inv; rewrite_fin_to_inf_dvalue; auto; cbn.
      { (* ix index *)
        cbn in *.
        break_match_hyp_inv; auto.
        - remember (0%Z) as n.
          clear Heqn Heqz.
          generalize dependent n.
          induction elts; intros n H0.
          + inv H0.
          + rewrite Z.eqb_refl in H0. inv H0.
        - remember (Z.pos p) as n.
          clear Heqn Heqz.
          generalize dependent n.
          induction elts; intros n H0.
          + inv H0.
          + cbn.
            break_match_hyp_inv.
      }
    }
  Qed.

  Lemma extract_value_loop_fin_inf_err :
    forall idxs str msg,
      (fix loop str idxs {struct idxs} : err_ub_oom dvalue :=
         match idxs with
         | [] => ret str
         | i :: tl =>
             v <- index_into_str_dv str i ;;
             loop v tl
         end) str idxs = ERR_unERR_UB_OOM msg ->
      (fix loop str idxs {struct idxs} : err_ub_oom DVCrev.DV2.dvalue :=
         match idxs with
         | [] => ret str
         | i :: tl =>
             v <- E1.DV.index_into_str_dv str i ;;
             loop v tl
         end) (fin_to_inf_dvalue str) idxs = ERR_unERR_UB_OOM msg.
  Proof.
    induction idxs;
      intros str res LOOP.
    - inv LOOP; auto.
    - cbn in LOOP.
      repeat break_match_hyp_inv.
      destruct unERR_UB_OOM, unEitherT, unEitherT, unEitherT, unIdent;
        inv Heqs.

      pose proof index_into_str_dv_fin_inf Heqe as INDEX.
      rewrite INDEX.
      cbn; auto.

      match goal with
      | H: EitherMonad.unEitherT
             (EitherMonad.unEitherT
                (EitherMonad.unEitherT
                   (Error.unERR_UB_OOM
                      (?L)))) = _ |- _ =>
          remember L as LOOP
      end.

      destruct_err_ub_oom LOOP; inv H1.
      symmetry in HeqLOOP.
      apply IHidxs in HeqLOOP.

      cbn.
      erewrite index_into_str_dv_fin_inf; eauto.
      remember {| unERR_UB_OOM := unERR_UB_OOM |} as x.
      destruct_err_ub_oom x; cbn in *; subst; inv Heqx; inv Heqs.
      setoid_rewrite HeqLOOP.
      reflexivity.
  Qed.

  Lemma eval_select_err_fin_inf :
    forall cond uv1_fin uv2_fin uv1_inf uv2_inf msg
      (IH1 : forall msg,
          IS2.MEM.CP.CONC.concretize_u uv1_fin (ERR_unERR_UB_OOM msg) ->
          IS1.MEM.CP.CONC.concretize_u uv1_inf (ERR_unERR_UB_OOM msg))
      (IH2 : forall msg,
          IS2.MEM.CP.CONC.concretize_u uv2_fin (ERR_unERR_UB_OOM msg) ->
          IS1.MEM.CP.CONC.concretize_u uv2_inf (ERR_unERR_UB_OOM msg)),
      uvalue_refine_strict uv1_inf uv1_fin ->
      uvalue_refine_strict uv2_inf uv2_fin ->
      @eval_select ErrUbOomProp Monad_ErrUbOomProp
        (fun (dt : dtyp) (edv : err_ub_oom dvalue) =>
           match unERR_UB_OOM edv with
           | {|
               EitherMonad.unEitherT :=
                 {|
                   EitherMonad.unEitherT :=
                     {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |}
                 |}
             |} => dvalue_has_dtyp dv dt /\ dv <> DVALUE_Poison dt
           | _ => True
           end) err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (fun (A : Type) (x ue : err_ub_oom A) => x = ue) cond uv1_fin uv2_fin (ERR_unERR_UB_OOM msg) ->
      @IS1.MEM.CP.CONC.eval_select ErrUbOomProp Monad_ErrUbOomProp
        (fun (dt : dtyp) (edv : err_ub_oom DVCrev.DV2.dvalue) =>
           match unERR_UB_OOM edv with
           | {|
               EitherMonad.unEitherT :=
                 {|
                   EitherMonad.unEitherT :=
                     {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |}
                 |}
             |} => E1.DV.dvalue_has_dtyp dv dt /\ dv <> E1.DV.DVALUE_Poison dt
           | _ => True
           end) err_ub_oom
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (fun (A : Type) (x ue : err_ub_oom A) => x = ue) (fin_to_inf_dvalue cond) uv1_inf uv2_inf (ERR_unERR_UB_OOM msg).
  Proof.
    intros cond uv1_fin uv2_fin uv1_inf uv2_inf msg IH1 IH2 REF1 REF2 EVAL.
    destruct cond.
    { unfold fin_to_inf_dvalue at 1.
      break_match_goal; clear Heqs; destruct p; clear e0;
      cbn in e; break_match_hyp_inv;
        cbn in *; subst; cbn in *; auto; inv EVAL; auto.
    }

    { (* integer conditional *)
      rewrite eval_select_equation in *.
      rewrite IS1.MEM.CP.CONC.eval_select_equation.
      rewrite fin_to_inf_dvalue_ix.

      repeat break_match_hyp; cbn in *;
        try inv EVAL; auto.
      - eapply IH1; eauto.
      - eapply IH2; eauto.
    }

    all: try solve
           [ unfold fin_to_inf_dvalue at 1;
             break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e;
             cbn in *; subst; cbn in *; inv EVAL; auto
           | unfold fin_to_inf_dvalue at 1;
             break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; inv e;
             cbn in *; subst; cbn in *; reflexivity
           | unfold fin_to_inf_dvalue at 1;
             break_match_goal; clear Heqs; destruct p; clear e0;
              cbn in e; break_match_hyp_inv;
             cbn in *; subst; cbn in *; auto; inv EVAL; auto
           ].

    { (* Vector conditional *)
      rewrite eval_select_equation in *.
      rewrite IS1.MEM.CP.CONC.eval_select_equation.

      rewrite_fin_to_inf_dvalue.
      repeat red.

      repeat red in EVAL.
      destruct EVAL as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { clear H1.
        exists (ERR_unERR_UB_OOM msg).
        exists (fun _ => ERR_unERR_UB_OOM msg).
        split; cbn; eauto.
        eapply IH1; eauto.
      }

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => ERR_unERR_UB_OOM msg).
      split.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.
      intros a ?; subst.
      repeat red.

      destruct H1 as [[] | H1].
      specialize (H1 _ eq_refl).
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { clear H2.
        exists (ERR_unERR_UB_OOM msg).
        exists (fun _ => ERR_unERR_UB_OOM msg).
        split; cbn; eauto.
        eapply IH2; eauto.
      }

      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => ERR_unERR_UB_OOM msg).
      split.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.
      intros a ?; subst.

      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).

      destruct x1;
        try (rewrite <- H2 in H5; inv H5);
        rewrite_fin_to_inf_dvalue; auto.

      destruct x3;
        try (rewrite <- H2 in H5; inv H5);
        rewrite_fin_to_inf_dvalue; auto.

      repeat red in H2.
      repeat red.

      destruct H2 as (?&?&?&?&?).
      rewrite <- H3 in H5.
      destruct_err_ub_oom x; inv H5.
      { exists (ERR_unERR_UB_OOM msg).
        exists (fun _ => ERR_unERR_UB_OOM msg).
        split; cbn; eauto.
        pose proof eval_select_loop_fin_inf elts elts0 elts1 (ERR_unERR_UB_OOM msg) as LOOP.
        specialize (LOOP H2).
        auto.
      }

      destruct H4 as [[] | H4].
      specialize (H4 _ eq_refl).
      cbn in H4.
      rewrite <- H4 in H7; inv H7.
    }
  Qed.

  Lemma concretize_uvalue_bytes_helper_err_fin_inf :
    forall uvs_inf uvs_fin acc_inf acc_fin msg
      (IH : forall (u : DV1.uvalue),
          Exists (DV1.uvalue_subterm u) uvs_inf ->
          forall uv_fin : DV2.uvalue,
            uvalue_refine_strict u uv_fin ->
            forall msg,
              IS2.MEM.CP.CONC.concretize_u uv_fin (ERR_unERR_UB_OOM msg) ->
              IS1.MEM.CP.CONC.concretize_u u (ERR_unERR_UB_OOM msg)),
      Forall2 uvalue_refine_strict uvs_inf uvs_fin ->
      concretization_map_refine acc_inf acc_fin ->
      @concretize_uvalue_bytes_helper ErrUbOomProp Monad_ErrUbOomProp
        (fun (dt : dtyp) (edv : err_ub_oom dvalue) =>
           match @unERR_UB_OOM IdentityMonad.ident dvalue edv with
           | {|
               EitherMonad.unEitherT :=
                 {|
                   EitherMonad.unEitherT :=
                     {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |}
                 |}
             |} => dvalue_has_dtyp dv dt /\ dv <> DVALUE_Poison dt
           | _ => True
           end) err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (fun (A : Type) (x ue : err_ub_oom A) => x = ue) acc_fin uvs_fin (ERR_unERR_UB_OOM msg) ->
      @IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalue_bytes_helper ErrUbOomProp Monad_ErrUbOomProp
        (fun (dt0 : dtyp) (edv : err_ub_oom IS1.LP.Events.DV.dvalue) =>
           match @unERR_UB_OOM IdentityMonad.ident IS1.LP.Events.DV.dvalue edv with
           | {|
               EitherMonad.unEitherT :=
                 {|
                   EitherMonad.unEitherT :=
                     {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |}
                 |}
             |} => IS1.LP.Events.DV.dvalue_has_dtyp dv dt0 /\ dv <> IS1.LP.Events.DV.DVALUE_Poison dt0
           | _ => True
           end) err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (fun (A : Type) (x ue : err_ub_oom A) => x = ue) acc_inf uvs_inf (ERR_unERR_UB_OOM msg).
  Proof.
    (* Will need something about acc_inf and acc_fin *)
    induction uvs_inf;
      intros uvs_fin acc_inf acc_fin msg IH REF ACC_REF CONC.
    - inv REF.
      cbn in CONC; inv CONC; cbn.
    - inv REF.
      rewrite concretize_uvalue_bytes_helper_equation in CONC.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalue_bytes_helper_equation.
      destruct y; uvalue_refine_strict_inv H1; try inv CONC; auto.
      rewrite pre_concretized_fin_inf with (uv_fin:=y) (acc_fin:=acc_fin); eauto.
      break_match_hyp_inv; repeat red.
      + (* pre-concretization exists *)
        destruct H as (?&?&?&?).
        destruct_err_ub_oom x0; inv H1.
        { exists (ERR_unERR_UB_OOM msg).
          exists (fun _ => ERR_unERR_UB_OOM msg).
          split; cbn; eauto.
        }

        destruct H2 as [[] | H2].
        specialize (H2 x2).
        forward H2; [cbn; auto|].
        rewrite <- H2 in H5.
        inv H5.
      + (* No pre-concretization exists *)
        destruct H as (?&?&?&?).
        destruct_err_ub_oom x0; inv H1.
        { exists (ERR_unERR_UB_OOM msg).
          exists (fun _ => ERR_unERR_UB_OOM msg).
          split; cbn; eauto.
          eapply IH; eauto.
          repeat constructor.
        }

        exists (ret (fin_to_inf_dvalue x2)).
        exists (fun _ => ERR_unERR_UB_OOM msg).
        split.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        split; cbn; eauto.
        right.
        intros ? ?; subst.
        repeat red.

        destruct H2 as [[] | H2].
        specialize (H2 x2).
        forward H2; [cbn; auto|].
        cbn in H2.
        repeat red in H2.
        destruct H2 as (?&?&?&?&?).
        rewrite <- H2 in H5.
        destruct_err_ub_oom x0; inv H5.
        { exists (ERR_unERR_UB_OOM msg).
          exists (fun _ => ERR_unERR_UB_OOM msg).
          split; cbn; eauto.
          eapply IHuvs_inf; eauto.
          eapply concretize_map_refine_new_concretized_byte_fin_inf; eauto.
          eapply fin_to_inf_dvalue_refine_strict.
        }

        exists (ret (fin_to_inf_dvalue_bytes x4)).
        exists (fun _ => ERR_unERR_UB_OOM msg).
        split.
        eapply concretize_uvalue_bytes_helper_fin_inf; eauto.
        intros u H5 uv_fin H6 dv_fin H8.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        eapply concretize_map_refine_new_concretized_byte_fin_inf; eauto.
        eapply fin_to_inf_dvalue_refine_strict.

        destruct H4 as [[] | H4].
        specialize (H4 x4).
        forward H4; [cbn; auto|].
        rewrite <- H4 in H7.
        inv H7.
  Qed.

  Lemma concretize_err_fin_inf :
    forall uv_inf uv_fin err_msg
      (REF : uvalue_refine_strict uv_inf uv_fin)
      (ERR: concretize_u uv_fin (ERR_unERR_UB_OOM err_msg)),
      IS1.LLVM.MEM.CP.CONC.concretize_u uv_inf (ERR_unERR_UB_OOM err_msg).
  Proof.
    induction uv_inf using DV1.uvalue_strong_ind;
      intros uv_fin err_msg REF ERR;
      try
        solve
        [ unfold_uvalue_refine_strict;
          try inv REF;
          repeat break_match_hyp_inv;
          repeat red in ERR;
          rewrite CONC.concretize_uvalueM_equation in ERR; inv ERR
        | cbn; auto
        ].

    destruct uv_inf;
      try
        solve
        [ unfold_uvalue_refine_strict;
          try inv REF;
          repeat break_match_hyp_inv;
          repeat red in ERR;
          rewrite CONC.concretize_uvalueM_equation in ERR; inv ERR
        | cbn; auto
        ].

    - (* Structs *)
      unfold_uvalue_refine_strict_in REF.
      break_match_hyp_inv.
      eapply map_monad_oom_Forall2 in Heqo.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; inv H1.
      { (* ERR when concretizing l *)
        clear H2.
        induction Heqo.
        - cbn in H0; inv H0.
        - rewrite map_monad_unfold in H0.
          repeat red in H0.
          destruct H0 as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H2.
          { clear H3.
            pose proof (H x).
            forward H2.
            repeat constructor.
            specialize (H2 y err_msg H1 H0).
            rewrite map_monad_unfold.
            repeat red.
            exists (ERR_unERR_UB_OOM err_msg).
            exists (fun _ => (ERR_unERR_UB_OOM err_msg)).

            split; cbn; eauto.
            exists (ERR_unERR_UB_OOM err_msg).
            exists (fun _ => (ERR_unERR_UB_OOM err_msg)).

            split; cbn; eauto.
          }

          (* No UB on first element *)
          destruct H3 as [[] | H3].
          specialize (H3 x3).
          forward H3; [cbn; auto|].
          destruct H3 as (?&?&?&?&?).
          rewrite <- H3 in H5.
          destruct_err_ub_oom x1; inv H5.
          2: {
            destruct H4 as [[] | H4].
            specialize (H4 x5); forward H4; [cbn;auto|].

            cbn in H4.
            rewrite <- H4 in H7.
            inv H7.
          }

          repeat red.
          exists (ERR_unERR_UB_OOM err_msg).
          exists (fun _ => (ERR_unERR_UB_OOM err_msg)).
          split; cbn; eauto.

          repeat red.
          pose proof uvalue_concretize_strict_concretize_inclusion _ _ H1 as INC.
          red in INC.
          specialize (INC _ H0).

          exists (ret (fin_to_inf_dvalue x3)).
          exists (fun _ => (ERR_unERR_UB_OOM err_msg)).
          split; cbn; eauto.
          split; cbn; eauto.
          right.
          intros a H5; subst.

          repeat red.
          exists (ERR_unERR_UB_OOM err_msg).
          exists (fun _ => (ERR_unERR_UB_OOM err_msg)).
          split; cbn; eauto.

          forward IHHeqo.
          intros u H5 uv_fin err_msg0 REF UB.
          eapply H; try right; eauto.
          { clear - H5.
            dependent induction H5.
            - inv H.
              constructor.
              constructor.
              right; auto.
            - specialize (IHclos_trans2 l eq_refl).
              eapply t_trans.
              apply H5_.
              apply IHclos_trans2.
          }

          forward IHHeqo; eauto.
          repeat red in IHHeqo.
          destruct IHHeqo as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H6; eauto.

          destruct H7 as [[] | H7].
          specialize (H7 x6); forward H7; [cbn;auto|].

          cbn in H7.
          rewrite <- H7 in H9.
          inv H9.
      }

      (* Concretizing fields succeeds, should be a contradiction *)
      destruct H2 as [[] | H2].
      specialize (H2 x1 eq_refl).
      cbn in H2.
      rewrite <- H2 in H4.
      cbn in H4. inv H4.
    - (* Packed structs *)
      unfold_uvalue_refine_strict_in REF.
      break_match_hyp_inv.
      eapply map_monad_oom_Forall2 in Heqo.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; inv H1.
      { (* ERR when concretizing l *)
        clear H2.
        induction Heqo.
        - cbn in H0; inv H0.
        - rewrite map_monad_unfold in H0.
          repeat red in H0.
          destruct H0 as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H2.
          { clear H3.
            pose proof (H x).
            forward H2.
            repeat constructor.
            specialize (H2 y err_msg H1 H0).

            rewrite map_monad_unfold.
            repeat red.
            exists (ERR_unERR_UB_OOM err_msg).
            exists (fun _ => (ERR_unERR_UB_OOM err_msg)).

            split; cbn; eauto.
            exists (ERR_unERR_UB_OOM err_msg).
            exists (fun _ => (ERR_unERR_UB_OOM err_msg)).

            split; cbn; eauto.
          }

          (* No ERR on first element *)
          destruct H3 as [[] | H3].
          specialize (H3 x3).
          forward H3; [cbn; auto|].
          destruct H3 as (?&?&?&?&?).
          rewrite <- H3 in H5.
          destruct_err_ub_oom x1; inv H5.
          2: {
            destruct H4 as [[] | H4].
            specialize (H4 x5); forward H4; [cbn;auto|].

            cbn in H4.
            rewrite <- H4 in H7.
            inv H7.
          }

          repeat red.
          exists (ERR_unERR_UB_OOM err_msg).
          exists (fun _ => (ERR_unERR_UB_OOM err_msg)).
          split; cbn; eauto.

          repeat red.
          pose proof uvalue_concretize_strict_concretize_inclusion _ _ H1 as INC.
          red in INC.
          specialize (INC _ H0).

          exists (ret (fin_to_inf_dvalue x3)).
          exists (fun _ => (ERR_unERR_UB_OOM err_msg)).
          split; cbn; eauto.
          split; cbn; eauto.
          right.
          intros a H5; subst.

          repeat red.
          exists (ERR_unERR_UB_OOM err_msg).
          exists (fun _ => (ERR_unERR_UB_OOM err_msg)).
          split; cbn; eauto.

          forward IHHeqo.
          intros u H5 uv_fin err_msg0 REF ERR.
          eapply H; try right; eauto.
          { clear - H5.
            dependent induction H5.
            - inv H.
              constructor.
              constructor.
              right; auto.
            - specialize (IHclos_trans2 l eq_refl).
              eapply t_trans.
              apply H5_.
              apply IHclos_trans2.
          }

          forward IHHeqo; eauto.
          repeat red in IHHeqo.
          destruct IHHeqo as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H6; eauto.

          destruct H7 as [[] | H7].
          specialize (H7 x6); forward H7; [cbn;auto|].

          cbn in H7.
          rewrite <- H7 in H9.
          inv H9.
      }

      (* Concretizing fields succeeds, should be a contradiction *)
      destruct H2 as [[] | H2].
      specialize (H2 x1 eq_refl).
      cbn in H2.
      rewrite <- H2 in H4.
      cbn in H4. inv H4.
    - (* Arrays *)
      unfold_uvalue_refine_strict_in REF.
      break_match_hyp_inv.
      eapply map_monad_oom_Forall2 in Heqo.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; inv H1.
      { (* ERR when concretizing l *)
        clear H2.
        induction Heqo.
        - cbn in H0; inv H0.
        - rewrite map_monad_unfold in H0.
          repeat red in H0.
          destruct H0 as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H2.
          { clear H3.
            pose proof (H x).
            forward H2.
            repeat constructor.
            specialize (H2 y err_msg H1 H0).
            rewrite map_monad_unfold.
            repeat red.
            exists (ERR_unERR_UB_OOM err_msg).
            exists (fun _ => (ERR_unERR_UB_OOM err_msg)).

            split; cbn; eauto.
            exists (ERR_unERR_UB_OOM err_msg).
            exists (fun _ => (ERR_unERR_UB_OOM err_msg)).

            split; cbn; eauto.
          }

          (* No ERR on first element *)
          destruct H3 as [[] | H3].
          specialize (H3 x3).
          forward H3; [cbn; auto|].
          destruct H3 as (?&?&?&?&?).
          rewrite <- H3 in H5.
          destruct_err_ub_oom x1; inv H5.
          2: {
            destruct H4 as [[] | H4].
            specialize (H4 x5); forward H4; [cbn;auto|].

            cbn in H4.
            rewrite <- H4 in H7.
            inv H7.
          }

          repeat red.
          exists (ERR_unERR_UB_OOM err_msg).
          exists (fun _ => (ERR_unERR_UB_OOM err_msg)).
          split; cbn; eauto.

          repeat red.
          pose proof uvalue_concretize_strict_concretize_inclusion _ _ H1 as INC.
          red in INC.
          specialize (INC _ H0).

          exists (ret (fin_to_inf_dvalue x3)).
          exists (fun _ => (ERR_unERR_UB_OOM err_msg)).
          split; cbn; eauto.
          split; cbn; eauto.
          right.
          intros a H5; subst.

          repeat red.
          exists (ERR_unERR_UB_OOM err_msg).
          exists (fun _ => (ERR_unERR_UB_OOM err_msg)).
          split; cbn; eauto.

          forward IHHeqo.
          intros u H5 uv_fin err_msg0 REF ERR.
          eapply H; try right; eauto.
          { clear - H5.
            dependent induction H5.
            - inv H.
              constructor.
              constructor.
              right; auto.
            - specialize (IHclos_trans2 t l eq_refl).
              eapply t_trans.
              apply H5_.
              apply IHclos_trans2.
          }
          forward IHHeqo; eauto.
          repeat red in IHHeqo.
          destruct IHHeqo as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H6; eauto.

          destruct H7 as [[] | H7].
          specialize (H7 x6); forward H7; [cbn;auto|].

          cbn in H7.
          rewrite <- H7 in H9.
          inv H9.
      }

      (* Concretizing fields succeeds, should be a contradiction *)
      destruct H2 as [[] | H2].
      specialize (H2 x1 eq_refl).
      cbn in H2.
      rewrite <- H2 in H4.
      cbn in H4. inv H4.
    - (* Vectors *)
      unfold_uvalue_refine_strict_in REF.
      break_match_hyp_inv.
      eapply map_monad_oom_Forall2 in Heqo.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; inv H1.
      { (* ERR when concretizing l *)
        clear H2.
        induction Heqo.
        - cbn in H0; inv H0.
        - rewrite map_monad_unfold in H0.
          repeat red in H0.
          destruct H0 as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H2.
          { clear H3.
            pose proof (H x).
            forward H2.
            repeat constructor.
            specialize (H2 y err_msg H1 H0).
            rewrite map_monad_unfold.
            repeat red.
            exists (ERR_unERR_UB_OOM err_msg).
            exists (fun _ => (ERR_unERR_UB_OOM err_msg)).

            split; cbn; eauto.
            exists (ERR_unERR_UB_OOM err_msg).
            exists (fun _ => (ERR_unERR_UB_OOM err_msg)).

            split; cbn; eauto.
          }

          (* No ERR on first element *)
          destruct H3 as [[] | H3].
          specialize (H3 x3).
          forward H3; [cbn; auto|].
          destruct H3 as (?&?&?&?&?).
          rewrite <- H3 in H5.
          destruct_err_ub_oom x1; inv H5.
          2: {
            destruct H4 as [[] | H4].
            specialize (H4 x5); forward H4; [cbn;auto|].

            cbn in H4.
            rewrite <- H4 in H7.
            inv H7.
          }

          repeat red.
          exists (ERR_unERR_UB_OOM err_msg).
          exists (fun _ => (ERR_unERR_UB_OOM err_msg)).
          split; cbn; eauto.

          repeat red.
          pose proof uvalue_concretize_strict_concretize_inclusion _ _ H1 as INC.
          red in INC.
          specialize (INC _ H0).

          exists (ret (fin_to_inf_dvalue x3)).
          exists (fun _ => (ERR_unERR_UB_OOM err_msg)).
          split; cbn; eauto.
          split; cbn; eauto.
          right.
          intros a H5; subst.

          repeat red.
          exists (ERR_unERR_UB_OOM err_msg).
          exists (fun _ => (ERR_unERR_UB_OOM err_msg)).
          split; cbn; eauto.

          forward IHHeqo.
          intros u H5 uv_fin err_msg0 REF ERR.
          eapply H; try right; eauto.
          { clear - H5.
            dependent induction H5.
            - inv H.
              constructor.
              constructor.
              right; auto.
            - specialize (IHclos_trans2 t l eq_refl).
              eapply t_trans.
              apply H5_.
              apply IHclos_trans2.
          }
          forward IHHeqo; eauto.
          repeat red in IHHeqo.
          destruct IHHeqo as (?&?&?&?&?).
          destruct_err_ub_oom x1; inv H6; eauto.

          destruct H7 as [[] | H7].
          specialize (H7 x6); forward H7; [cbn;auto|].

          cbn in H7.
          rewrite <- H7 in H9.
          inv H9.
      }

      (* Concretizing fields succeeds, should be a contradiction *)
      destruct H2 as [[] | H2].
      specialize (H2 x1 eq_refl).
      cbn in H2.
      rewrite <- H2 in H4.
      cbn in H4. inv H4.
    - (* UVALUE_ICmp *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* ERR when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No ERR on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* ERR in second operand *)
        eapply IH in H0; eauto.
        repeat red.
        exists (ret (fin_to_inf_dvalue x1)).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        split; eauto.
        right.
        intros a H3.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* ERR in evaluating operation? *)
      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      rewrite <- H2 in H5.

      remember (eval_iop iop x1 x3) as res.
      destruct_err_ub_oom res; inv H5.

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      eapply eval_iop_err_fin_inf; eauto.
    - (* UVALUE_ICmp *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* ERR when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No ERR on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* ERR in second operand *)
        eapply IH in H0; eauto.
        repeat red.
        exists (ret (fin_to_inf_dvalue x1)).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        split; eauto.
        right.
        intros a H3.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* ERR in evaluating operation? *)
      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      rewrite <- H2 in H5.

      remember (eval_icmp cmp x1 x3) as res.
      destruct_err_ub_oom res; inv H5.

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      eapply eval_icmp_err_fin_inf; eauto.
    - (* UVALUE_FBinop *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* ERR when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No ERR on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* ERR in second operand *)
        eapply IH in H0; eauto.
        repeat red.
        exists (ret (fin_to_inf_dvalue x1)).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        split; eauto.
        right.
        intros a H3.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* ERR in evaluating operation? *)
      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      rewrite <- H2 in H5.

      remember (eval_fop fop x1 x3) as res.
      destruct_err_ub_oom res; inv H5.

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      eapply eval_fop_err_fin_inf; eauto.
    - (* UVALUE_FCmp *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* ERR when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No ERR on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* ERR in second operand *)
        eapply IH in H0; eauto.
        repeat red.
        exists (ret (fin_to_inf_dvalue x1)).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        split; eauto.
        right.
        intros a H3.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* ERR in evaluating operation? *)
      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      rewrite <- H2 in H5.

      remember (eval_fcmp cmp x1 x3) as res.
      destruct_err_ub_oom res; inv H5.

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).

      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.

      intros a H3; subst.
      eapply eval_fcmp_err_fin_inf; eauto.
    - (* UVALUE_Conversion *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* ERR when concretizing uv *)
        eapply IH in H; eauto.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No ERR on concretizing uv. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).
      split.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.
      intros a H0; subst.
      break_match_hyp.

      { (* Pure *)
        cbn in H1.
        rewrite <- H1 in H3; inv H3.
      }

      { (* ItoP *)
        break_match_hyp;
        cbn in H1;
        rewrite <- H1 in H3; inv H3.
      }

      { (* PtoI *)
        erewrite get_conv_case_ptoi_fin_inf; eauto.
        cbn.
        repeat break_match_hyp;
          cbn in H1;
          rewrite <- H1 in H3; inv H3;
          rewrite_fin_to_inf_dvalue; auto.
        - erewrite ptr_to_int_fin_to_inf_addr; eauto.
          unfold lift_OOM in *.
          break_inner_match_hyp;
            cbn in *; inv H2.
      }

      { (* Oom *)
        rewrite <- H1 in H3; inv H3.
      }

      { (* Illegal *)
        rewrite <- H1 in H3; inv H3.
        erewrite get_conv_case_illegal_fin_inf; eauto.
      }
    - (* UVALUE_GetElementPtr *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* ERR when concretizing base address *)
        eapply IH in H; eauto.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No ERR on base address. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).
      split; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; cbn; eauto.
      right.
      intros a ?; subst.
      repeat red.

      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.
      { (* ERR in concretization of indices *)
        clear H2.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split.
        (* TODO: Probably make a map_monad lemma *)
        { clear - IH H0 Heqo0.
          generalize dependent l.
          induction idxs;
            intros l H0 Heqo0.
          - inv Heqo0. inv H0.
          - rewrite map_monad_unfold in *.
            cbn in Heqo0.
            repeat break_match_hyp_inv.

            rewrite map_monad_unfold in H0.
            repeat red in H0.

            destruct H0 as (?&?&?&?&?).
            destruct_err_ub_oom x; inv H0.
            { (* ERR in first index *)
              clear H1.
              repeat red.
              exists (ERR_unERR_UB_OOM err_msg).
              exists (fun _ => ERR_unERR_UB_OOM err_msg).
              split; cbn; eauto.
              eapply IH; eauto.
              repeat constructor.
            }

            (* ERR in map *)
            exists (ret (fin_to_inf_dvalue x1)).
            exists (fun _ => ERR_unERR_UB_OOM err_msg).
            split; cbn; eauto.
            eapply uvalue_concretize_strict_concretize_inclusion; eauto.
            split; cbn; eauto.
            right.
            intros a0 H8; subst.

            destruct H1 as [[] | H1].
            specialize (H1 x1).
            forward H1; [cbn; auto|].
            repeat red in H1.
            destruct H1 as (?&?&?&?&?).
            rewrite <- H1 in H3.
            destruct_err_ub_oom x; inv H3.
            { clear H2.
              repeat red.
              exists (ERR_unERR_UB_OOM err_msg).
              exists (fun _ => (ERR_unERR_UB_OOM err_msg)).
              split.
              { eapply IHidxs; eauto.
                intros u0 H2 uv_fin err_msg0 REF ERR.
                eapply IH; eauto.
                clear - H2.
                dependent induction H2.
                - inv H.
                  repeat constructor; auto.
                  constructor.
                  constructor.
                  right; auto.
                - specialize (IHclos_trans2 t uv_inf idxs eq_refl).
                  eapply t_trans.
                  apply H2_.
                  apply IHclos_trans2.
              }

              split; cbn; eauto.
            }

            exfalso.
            destruct H2 as [[] | H2].
            specialize (H2 x3).
            forward H2; [cbn; auto|].
            rewrite <- H2 in H5.
            inv H5.
        }

        split; cbn; eauto.
      }

      (* No ERR when concretizing indices... *)
      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      repeat break_match_hyp;
        rewrite <- H2 in H5; inv H5.

      (* Error in handle_gep *)
      exists (ret (fmap fin_to_inf_dvalue x3)).
      exists (fun _ => (ERR_unERR_UB_OOM err_msg)).
      split; cbn; eauto.

      (* TODO: Probably make a map_monad lemma *)
      { clear - IH H0 Heqo0.
        generalize dependent l.
        generalize dependent x3.
        induction idxs;
          intros x3 l H0 Heqo0.
        - inv Heqo0. inv H0.
          cbn.
          reflexivity.
        - rewrite map_monad_unfold in *.
          cbn in Heqo0.
          repeat break_match_hyp_inv.

          rewrite map_monad_unfold in H0.
          repeat red in H0.

          destruct H0 as (?&?&?&?&?).
          destruct_err_ub_oom x; inv H0.
          repeat red.
          exists (ret (fin_to_inf_dvalue x1)).
          exists (fun _ => ret (flat_map (fun x : DVCrev.DV1.dvalue => [fin_to_inf_dvalue x]) x3)).
          split; cbn; eauto.
          eapply uvalue_concretize_strict_concretize_inclusion; eauto.
          split; cbn; eauto.
          right.
          intros a0 H8; subst.

          destruct H1 as [[] | H1].
          specialize (H1 x1).
          forward H1; [cbn; auto|].
          repeat red in H1.
          destruct H1 as (?&?&?&?&?).
          rewrite <- H1 in H3.
          destruct_err_ub_oom x; inv H3.

          destruct H2 as [[] | H2].
          specialize (H2 x4).
          forward H2; [cbn; auto|].
          rewrite <- H2 in H5.
          inv H5.
          cbn in H2.

          repeat red.
          exists (ret (fmap fin_to_inf_dvalue x4)).
          exists (fun _ => ret (flat_map (fun x : DVCrev.DV1.dvalue => [fin_to_inf_dvalue x]) (x1 :: x4))).
          split; cbn; eauto.
          2: {
            split; cbn; eauto.
            right.
            intros a0 H3; subst.
            reflexivity.
          }

          eapply IHidxs; eauto.
          intros u0 H3 uv_fin err_msg REF ERR.
          eapply IH; eauto.

          { clear - H3.
            dependent induction H3.
            - inv H.
              repeat constructor; auto.
              constructor.
              constructor.
              right; auto.
            - specialize (IHclos_trans2 t uv_inf idxs eq_refl).
              eapply t_trans.
              apply H3_.
              apply IHclos_trans2.
          }
      }

      split; cbn; eauto.
      right.
      intros ? ?; subst.
      destruct x1;
        rewrite_fin_to_inf_dvalue;
        try solve [cbn; inv Heqs; auto].
      cbn in *.
      break_match_hyp_inv.
      erewrite handle_gep_addr_err_fin_inf; eauto.
      unfold fin_to_inf_addr.
      break_match_goal.
      clear Heqs; auto.
    - (* UVALUE_ExtractElement *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* ERR when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).
      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a ?; subst.
      repeat red.

      (* No ERR on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* ERR in second operand *)
        eapply IH in H0; eauto.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).
      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a ?; subst.
      repeat red.

      (* ERR in evaluating operation? *)
      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      repeat red in H2.
      destruct H2 as (?&?&?&?&?).
      rewrite <- H3 in H5.
      destruct_err_ub_oom x; inv H5.
      { (* non-vector type... *)
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
      }

      exists (ret x5).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).
      split; cbn; eauto.
      split; eauto.
      right.
      intros ? ?; subst. 

      destruct H4 as [[] | H4].
      specialize (H4 a).
      forward H4; [cbn; auto|].
      cbn in H3.
      remember (index_into_vec_dv a x1 x3) as res.
      rewrite <- H4 in H7.
      destruct_err_ub_oom res; inv H7.
      symmetry in Heqres.
      eapply index_into_vec_dv_err_fin_inf in Heqres; eauto.
    - (* UVALUE_InsertElement *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* ERR when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).
      split; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a H0.
      inv H0.

      (* No ERR on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* ERR uv_inf3 *)
        eapply IH in H0; eauto.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No ERR on uv_inf3 *)
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).
      split; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a ?.
      inv H3.

      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      repeat red in H2.
      destruct H2 as (?&?&?&?&?).
      rewrite <- H3 in H5.
      destruct_err_ub_oom x; inv H5.

      { (* ERR in uv_inf2 *)
        eapply IH in H2; eauto.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No ERR on uv_inf2 *)
      exists (ret (fin_to_inf_dvalue x5)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).
      split; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a ?.
      inv H5.

      (* ERR in evaluating... *)
      destruct H4 as [[] | H4].
      specialize (H4 x5).
      forward H4; [cbn; auto|].
      rewrite <- H4 in H7.
      remember (insert_into_vec_dv vec_typ x1 x5 x3) as res.
      destruct_err_ub_oom res; inv H7.
      symmetry in Heqres.
      eapply insert_into_vec_dv_err_fin_inf in Heqres; eauto.
    - (* UVALUE_ShuffleVector *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR; inv ERR.
      reflexivity.
    - (* UVALUE_ExtractValue *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* ERR when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No ERR on first operand. *)
      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).
      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a ?; subst.
      repeat red.

      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      remember (x0 x1) as x0x1.
      destruct_err_ub_oom x0x1; inv H3.
      eapply extract_value_loop_fin_inf_err in H1.
      setoid_rewrite H1.
      reflexivity.
    - (* UVALUE_InsertValue *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* ERR when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No ERR on first operand. *)
      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).
      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a ?; subst.
      repeat red.

      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      rewrite <- H1 in H3.
      destruct_err_ub_oom x; inv H3.

      { (* UB in second operand *)
        eapply IH in H0; eauto.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      (* No UB on second operand. *)
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).
      split; cbn; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a ?; subst.
      repeat red.

      (* UB in evaluating operation? *)
      destruct H2 as [[] | H2].
      specialize (H2 x3).
      forward H2; [cbn; auto|].
      repeat red in H2.

      pose proof H2 as LOOP.
      apply insert_value_loop_fin_inf_succeeds in LOOP.
      cbn in LOOP.
      rewrite LOOP.
      remember (x2 x3) as res.
      destruct_err_ub_oom res; inv H5.
      reflexivity.
    - (* UVALUE_Select *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.

      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { (* ERR when concretizing first operand *)
        eapply IH in H; eauto.
        repeat red.
        exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        repeat constructor.
      }

      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).
      split; eauto.
      eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      split; eauto.
      right.
      intros a H0.
      inv H0.

      (* No ERR on first operand. *)
      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      remember (x0 x1) as res.
      destruct_err_ub_oom res; inv H3; eauto.
      epose proof eval_select_err_fin_inf x1 u0 u1 uv_inf2 uv_inf3 _ as EVAL.
      forward EVAL; [intros ? ?; eapply IH; eauto; repeat constructor|].
      forward EVAL; [intros ? ?; eapply IH; eauto; repeat constructor|].
      forward EVAL; eauto.
      forward EVAL; eauto.
      forward EVAL.
      { rewrite eval_select_equation.
        cbn in *; eauto.
      }

      rewrite IS1.MEM.CP.CONC.eval_select_equation in EVAL.
      auto.
    - (* UVALUE_ExtractByte *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.
      inv ERR.
      cbn. auto.
    - (* UVALUE_ConcatBytes *)
      rename H into IH.
      unfold_uvalue_refine_strict_in REF.
      repeat break_match_hyp_inv.

      repeat red.
      rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation.

      repeat red in ERR.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in ERR.
      auto.

      erewrite map_monad_oom_length; eauto.
      erewrite sizeof_dtyp_fin_inf; eauto.
      erewrite all_extract_bytes_from_uvalue_fin_inf; eauto.
      break_match_hyp.
      2: {
        cbn.
        cbn in ERR.
        repeat red in ERR.
        destruct ERR as (?&?&?&?&?).
        destruct_err_ub_oom x; inv H0.
        { exists (ERR_unERR_UB_OOM err_msg).
          exists (fun _ => ERR_unERR_UB_OOM err_msg).
          split; cbn; eauto.
          eapply concretize_uvalue_bytes_helper_err_fin_inf; eauto.
          2: eapply map_monad_oom_Forall2; eauto.
          2: apply concretization_map_refine_empty.

          intros u H0 uv_fin H2 ub_msg0 H3.
          eapply IH; eauto.
          eapply IS1.LP.Events.DV.uvalue_concat_bytes_strict_subterm; eauto.
        }

        destruct H1 as [[] | H1].
        specialize (H1 x1).
        forward H1; [cbn; auto|].
        remember (x0 x1) as x0x1.
        destruct_err_ub_oom x0x1; inv H3.

        eapply concretize_uvalue_bytes_helper_fin_inf in H; eauto.
        3: eapply map_monad_oom_Forall2; eauto.
        2: {
          intros u H0 uv_fin H2 dv_fin H3.
          eapply uvalue_concretize_strict_concretize_inclusion; eauto.
        }

        exists (ret (fin_to_inf_dvalue_bytes x1)).
        exists (fun _ => ERR_unERR_UB_OOM err_msg).
        split; eauto.
        split; eauto.
        right.
        intros a RETa.
        inv RETa.
        eapply dvalue_bytes_to_dvalue_err_fin_inf; eauto.
        apply dvalue_bytes_refine_fin_to_inf_dvalue_bytes.
        apply concretization_map_refine_empty.
      }
      pose proof (map_monad_oom_length _ _ _ Heqo) as LEN.

      break_match_hyp.
      { (* ERR when concretizing first operand *)
        destruct uvs.
        { inv Heqo.
          cbn in Heqo0; inv Heqo0.
        }
        rewrite map_monad_unfold in Heqo.
        cbn in Heqo.
        repeat break_match_hyp_inv.
        destruct u1; inv Heqo0.
        repeat break_match_hyp_inv.
        unfold OptionUtil.guard_opt in *.
        repeat break_match_hyp_inv.
        apply dtyp_eqb_eq in Heqb4; subst.
        rewrite H1; cbn.

        uvalue_convert_strict_inv Heqo1.
        eapply IH; eauto.
        eapply IS1.LP.Events.DV.uvalue_concat_bytes_strict_subterm; eauto.
        repeat constructor.
      }

      cbn.
      cbn in ERR.
      repeat red in ERR.
      destruct ERR as (?&?&?&?&?).
      destruct_err_ub_oom x; inv H0.
      { exists (ERR_unERR_UB_OOM err_msg).
        exists (fun _ => UB_unERR_UB_OOM err_msg).
        split; cbn; eauto.
        eapply concretize_uvalue_bytes_helper_err_fin_inf; eauto.
        2: eapply map_monad_oom_Forall2; eauto.
        2: eapply concretization_map_refine_empty.

        intros u H0 uv_fin H2 ub_msg0 H3.
        eapply IH; eauto.
        eapply DV1.uvalue_concat_bytes_strict_subterm; auto.
      }

      destruct H1 as [[] | H1].
      specialize (H1 x1).
      forward H1; [cbn; auto|].
      remember (x0 x1) as x0x1.
      destruct_err_ub_oom x0x1; inv H3.

      eapply concretize_uvalue_bytes_helper_fin_inf in H; eauto.
      3: eapply map_monad_oom_Forall2; eauto.
      2: {
        intros u H0 uv_fin H2 dv_fin H3.
        eapply uvalue_concretize_strict_concretize_inclusion; eauto.
      }

      exists (ret (fin_to_inf_dvalue_bytes x1)).
      exists (fun _ => ERR_unERR_UB_OOM err_msg).
      split; eauto.
      split; eauto.
      right.
      intros a RETa.
      inv RETa.
      eapply dvalue_bytes_to_dvalue_err_fin_inf; eauto.
      apply dvalue_bytes_refine_fin_to_inf_dvalue_bytes.

      apply concretization_map_refine_empty.
  Qed.

  Lemma concretize_no_err_inf_fin :
    forall uv_inf uv_fin
      (REF : uvalue_refine_strict uv_inf uv_fin)
      (ERR : forall err_msg : string, ~ IS1.LLVM.MEM.CP.CONC.concretize_u uv_inf (ERR_unERR_UB_OOM err_msg)),
    forall err_msg : string, ~ concretize_u uv_fin (ERR_unERR_UB_OOM err_msg).
  Proof.
    intros uv_inf uv_fin REF ERR err_msg.
    intros CONC.
    eapply ERR;
      eapply concretize_err_fin_inf; eauto.
  Qed.

  Lemma uvalue_refine_strict_unique_prop :
    forall uv_inf uv_fin,
      uvalue_refine_strict uv_inf uv_fin ->
      IS1.LLVM.Pick.unique_prop uv_inf ->
      unique_prop uv_fin.
  Proof.
    intros uv_inf uv_fin REF UNIQUE_INF.

    unfold unique_prop.
    unfold IS1.LLVM.Pick.unique_prop in UNIQUE_INF.
    destruct UNIQUE_INF as [NUB [NERR [[dv_inf [CONC UNIQUE_INF]] | NO_CONC]]].
    2: {
      split.
      eapply concretize_no_ub_inf_fin; eauto.
      split.
      eapply concretize_no_err_inf_fin; eauto.
      right.
      eapply concretize_fails_inf_fin; eauto.
    }

    pose proof uvalue_concretize_strict_concretize_inclusion _ _ REF.
    red in H.

    pose proof concretize_inf_excluded_middle uv_fin.
    destruct H0 as [(dv_fin & CONC_FIN) | H0]; auto.
    all:
      split;
      [ eapply concretize_no_ub_inf_fin; eauto
      | split;
        [eapply concretize_no_err_inf_fin|];
        eauto].

    left.
    exists dv_fin.
    split; eauto.
    intros dv H1.
    apply H in H1, CONC_FIN.
    apply UNIQUE_INF in H1, CONC_FIN.
    subst.
    apply fin_to_inf_dvalue_injective in H1;
      subst; auto.
  Qed.

  (*
    - fin_to_inf_dvalue_injective
    - concretize_no_err_inf_fin
    - concretize_no_err_inf_fin
   *)

  Lemma uvalue_refine_strict_non_poison_prop :
    forall uv_inf uv_fin,
      uvalue_refine_strict uv_inf uv_fin ->
      IS1.LLVM.Pick.non_poison_prop uv_inf ->
      non_poison_prop uv_fin.
  Proof.
    intros uv_inf uv_fin REF NON_POISON_INF.

    unfold non_poison_prop.
    unfold IS1.LLVM.Pick.non_poison_prop in NON_POISON_INF.
    destruct NON_POISON_INF as [NUB [NERR NON_POISON_INF]].
    split.
    eapply concretize_no_ub_inf_fin; eauto.
    split.
    eapply concretize_no_err_inf_fin; eauto.

    intros dt CONTRA.
    eapply (NON_POISON_INF dt).

    replace (IS1.LP.Events.DV.DVALUE_Poison dt) with
      (fin_to_inf_dvalue (DVALUE_Poison dt)).
    2: {
      unfold fin_to_inf_dvalue.
      break_match_goal; subst.
      destruct p.
      unfold DVCrev.dvalue_convert_strict in e.
      cbn in *.
      clear Heqs.
      inv e.
      auto.
    }

    eapply uvalue_concretize_strict_concretize_inclusion.
    apply REF.
    apply CONTRA.
  Qed.

  Lemma lift_err_uvalue_to_dvalue_rutt_strict :
    forall uv1 uv2,
      uvalue_refine_strict uv1 uv2 ->
      rutt (sum_prerel call_refine_strict event_refine_strict) (sum_postrel call_res_refine_strict event_res_refine_strict) dvalue_refine_strict
        (LLVMEvents.lift_err (fun x : IS1.LP.Events.DV.dvalue => Ret x) (IS1.LP.Events.DV.uvalue_to_dvalue uv1))
        (LLVMEvents.lift_err (fun x : dvalue => Ret x) (uvalue_to_dvalue uv2)).
  Proof.
    intros uv1 uv2 H.
    destruct uv1; cbn in *;
      try solve
        [ unfold uvalue_refine_strict in *;
          cbn in *; inv H; cbn;
          apply rutt_Ret;
          unfold dvalue_refine_strict; reflexivity
        | unfold uvalue_refine_strict in *;
          cbn in *; inv H; cbn;
          apply rutt_raise; constructor; cbn; auto
        | unfold uvalue_refine_strict in *;
          cbn in *;
          repeat break_match_hyp_inv;
          cbn;
          apply rutt_Ret;
          unfold dvalue_refine_strict;
          cbn;
          rewrite Heqo;
          reflexivity
        | unfold uvalue_refine_strict in *;
          cbn in *;
          repeat break_match_hyp_inv;
          cbn;
          apply rutt_raise;
          constructor;
          constructor
        ].

    - (* Structs *)
      unfold uvalue_refine_strict in H.
      cbn in *.
      break_match_hyp_inv.
      assert (uvalue_refine_strict (DV1.UVALUE_Struct fields) (DV2.UVALUE_Struct l)) as REF.
      { unfold uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }
      break_match_goal; cbn.
      { epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp_inv.

        cbn.
        apply rutt_raise.
        constructor.
        constructor.
      }
      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply rutt_Ret.
      unfold dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp_inv.
      unfold dvalue_refine_strict in H2.
      cbn in H2.
      break_match_hyp_inv.
      inversion Heqs0.
      reflexivity.

    - (* Packed Structs *)
      unfold uvalue_refine_strict in H.
      cbn in *.
      break_match_hyp_inv.

      assert (uvalue_refine_strict (DV1.UVALUE_Struct fields) (DV2.UVALUE_Struct l)) as REF.
      { unfold uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal; cbn.
      { epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp_inv.

        cbn.
        apply rutt_raise.
        constructor.
        constructor.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply rutt_Ret.
      unfold dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp_inv.
      unfold dvalue_refine_strict.
      unfold dvalue_refine_strict in H2.
      cbn in H2.
      break_match_hyp_inv.
      inversion Heqs0.
      reflexivity.

    - (* Arrays *)
      unfold uvalue_refine_strict in H.
      cbn in *.
      break_match_hyp_inv.

      assert (uvalue_refine_strict (DV1.UVALUE_Array t elts) (DV2.UVALUE_Array t l)) as REF.
      { unfold uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal; cbn.
      { epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp_inv.

        cbn.
        apply rutt_raise.
        constructor.
        constructor.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply rutt_Ret.
      unfold dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp_inv.
      unfold dvalue_refine_strict.
      unfold dvalue_refine_strict in H2.
      cbn in H2.
      break_match_hyp_inv.
      inversion Heqs0.
      reflexivity.

    - (* Vectors *)
      unfold uvalue_refine_strict in H.
      cbn in *.
      break_match_hyp_inv.

      assert (uvalue_refine_strict (DV1.UVALUE_Array t elts) (DV2.UVALUE_Array t l)) as REF.
      { unfold uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal; cbn.
      { epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp_inv.

        cbn.
        apply rutt_raise.
        constructor.
        constructor.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply rutt_Ret.
      unfold dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp_inv.
      unfold dvalue_refine_strict.
      unfold dvalue_refine_strict in H2.
      cbn in H2.
      break_match_hyp_inv.
      inversion Heqs0.
      reflexivity.
  Qed.

  Lemma lift_err_uvalue_to_dvalue_orutt_strict :
    forall uv1 uv2,
      uvalue_refine_strict uv1 uv2 ->
      orutt (sum_prerel call_refine_strict event_refine_strict) (sum_postrel call_res_refine_strict event_res_refine_strict) dvalue_refine_strict
        (LLVMEvents.lift_err (fun x : IS1.LP.Events.DV.dvalue => Ret x) (IS1.LP.Events.DV.uvalue_to_dvalue uv1))
        (LLVMEvents.lift_err (fun x : dvalue => Ret x) (uvalue_to_dvalue uv2))
        (OOM:=OOME).
  Proof.
    intros uv1 uv2 H.
    destruct uv1; cbn in *;
      try solve
        [ unfold uvalue_refine_strict in *;
          cbn in *; inv H; cbn;
          apply orutt_Ret;
          unfold dvalue_refine_strict; reflexivity
        | unfold uvalue_refine_strict in *;
          cbn in *; inv H; cbn;
          apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; cbn; auto
          ]
        | unfold uvalue_refine_strict in *;
          cbn in *;
          repeat break_match_hyp_inv;
          cbn;
          apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; cbn; auto
          ]
        | unfold uvalue_refine_strict in H;
          cbn in *;
          break_match_hyp_inv;
          cbn;
          apply orutt_Ret;
          unfold dvalue_refine_strict;
          cbn;
          rewrite Heqo;
          reflexivity
        ].

    - (* Structs *)
      unfold uvalue_refine_strict in H.
      cbn in *.
      break_match_hyp_inv.

      assert (uvalue_refine_strict (DV1.UVALUE_Struct fields) (DV2.UVALUE_Struct l)) as REF.
      { unfold uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp; inv H.

        cbn.
        apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ].
      }

      cbn.
      break_match_goal.
      { (* Probably a contradiction? *)
        cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply orutt_Ret.
      unfold dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp; inv H1.
      unfold dvalue_refine_strict in *.
      cbn in *.
      break_match_goal.
      2: {
        (* Contradiction *)
        exfalso.
        inv H2.
      }

      cbn in *.
      inv H2; inv Heqs0.
      reflexivity.

    - (* Packed Structs *)
      unfold uvalue_refine_strict in H.
      cbn in *.
      break_match_hyp_inv.

      assert (uvalue_refine_strict (DV1.UVALUE_Struct fields) (DV2.UVALUE_Struct l)) as REF.
      { unfold uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp; inv H.

        cbn.
        apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ].
      }

      cbn.
      break_match_goal.
      { (* Probably a contradiction? *)
        cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply orutt_Ret.
      unfold dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp; inv H1.
      unfold dvalue_refine_strict in *.
      cbn in *.
      break_match_goal.
      2: {
        (* Contradiction *)
        exfalso.
        inv H2.
      }

      cbn in *.
      inv H2; inv Heqs0.
      reflexivity.

    - (* Arrays *)
      unfold uvalue_refine_strict in H.
      cbn in *.
      break_match_hyp_inv.

      assert (uvalue_refine_strict (DV1.UVALUE_Array t elts) (DV2.UVALUE_Array t l)) as REF.
      { unfold uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp; inv H.

        cbn.
        apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ].
      }

      cbn.
      break_match_goal.
      { (* Probably a contradiction? *)
        cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply orutt_Ret.
      unfold dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp; inv H1.
      unfold dvalue_refine_strict in *.
      cbn in *.
      break_match_goal.
      2: {
        (* Contradiction *)
        exfalso.
        inv H2.
      }

      cbn in *.
      inv H2; inv Heqs0.
      reflexivity.

    - (* Vectors *)
      unfold uvalue_refine_strict in H.
      cbn in *.
      break_match_hyp_inv.

      assert (uvalue_refine_strict (DV1.UVALUE_Array t elts) (DV2.UVALUE_Array t l)) as REF.
      { unfold uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp; inv H.

        cbn.
        apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ].
      }

      cbn.
      break_match_goal.
      { (* Probably a contradiction? *)
        cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply orutt_Ret.
      unfold dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp; inv H1.
      unfold dvalue_refine_strict in *.
      cbn in *.
      break_match_goal.
      2: {
        (* Contradiction *)
        exfalso.
        inv H2.
      }

      cbn in *.
      inv H2; inv Heqs0.
      reflexivity.
Qed.

  Lemma lift_err_uvalue_to_dvalue_orutt_strict_instr_E :
    forall uv1 uv2,
      uvalue_refine_strict uv1 uv2 ->
      orutt instr_E_refine_strict instr_E_res_refine_strict dvalue_refine_strict
        (LLVMEvents.lift_err (fun x : IS1.LP.Events.DV.dvalue => Ret x) (IS1.LP.Events.DV.uvalue_to_dvalue uv1))
        (LLVMEvents.lift_err (fun x : dvalue => Ret x) (uvalue_to_dvalue uv2))
        (OOM:=OOME).
  Proof.
    intros uv1 uv2 H.
    destruct uv1; cbn in *;
      try solve
        [ unfold_uvalue_refine_strict_in H;
          cbn in *; inv H; cbn;
          apply orutt_Ret;
          unfold_dvalue_refine_strict_goal; reflexivity
        | unfold_uvalue_refine_strict_in H;
          cbn in *; inv H; cbn;
          apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; cbn; auto
          ]
        | unfold_uvalue_refine_strict_in H;
          cbn in *;
          break_match_hyp; inv H;
          break_match_hyp; inv H1;
          cbn;
          apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ]
        | unfold_uvalue_refine_strict;
          cbn in *;
          break_match_hyp; inv H;
          cbn;
          apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ]
        | unfold_uvalue_refine_strict;
          cbn in *;
          break_match_hyp; inv H;
          break_match_hyp; inv H1;
          break_match_hyp; inv H0;
          cbn;
          apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ]
        ].
    - unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.
      cbn.
      apply orutt_Ret.
      unfold_dvalue_refine_strict_goal.
      rewrite Heqo.
      cbn.
      reflexivity.
    - unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.
      cbn.
      apply orutt_Ret.
      unfold_dvalue_refine_strict_goal.
      cbn.
      rewrite Heqo.
      reflexivity.
    - (* Structs *)
      unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.

      assert (uvalue_refine_strict (DV1.UVALUE_Struct fields) (DV2.UVALUE_Struct l)) as REF.
      { unfold_uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp; inv H.

        cbn.
        apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ].
      }

      cbn.
      break_match_goal.
      { (* Probably a contradiction? *)
        cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply orutt_Ret.
      unfold_dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp; inv H1.
      unfold_dvalue_refine_strict.
      break_match_goal.
      2: {
        (* Contradiction *)
        exfalso.
        cbn in H2.
        inv H2.
      }

      cbn in *.
      inv H2; inv Heqs0.
      reflexivity.
    - (* Packed Structs *)
      unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.

      assert (uvalue_refine_strict (DV1.UVALUE_Struct fields) (DV2.UVALUE_Struct l)) as REF.
      { unfold_uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp; inv H.

        cbn.
        apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ].
      }

      cbn.
      break_match_goal.
      { (* Probably a contradiction? *)
        cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply orutt_Ret.
      unfold_dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp; inv H1.
      unfold_dvalue_refine_strict.
      break_match_goal.
      2: {
        (* Contradiction *)
        exfalso.
        cbn in H2.
        inv H2.
      }

      cbn in *.
      inv H2; inv Heqs0.
      reflexivity.
    - (* Arrays *)
      unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.

      assert (uvalue_refine_strict (DV1.UVALUE_Array t elts) (DV2.UVALUE_Array t l)) as REF.
      { unfold_uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp; inv H.

        cbn.
        apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ].
      }

      cbn.
      break_match_goal.
      { (* Probably a contradiction? *)
        cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply orutt_Ret.
      unfold_dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp; inv H1.
      unfold_dvalue_refine_strict.
      break_match_goal.
      2: {
        (* Contradiction *)
        exfalso.
        cbn in H2.
        inv H2.
      }

      cbn in *.
      inv H2; inv Heqs0.
      reflexivity.
    - (* Vectors *)
      unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.

      assert (uvalue_refine_strict (DV1.UVALUE_Array t elts) (DV2.UVALUE_Array t l)) as REF.
      { unfold_uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp; inv H.

        cbn.
        apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ].
      }

      cbn.
      break_match_goal.
      { (* Probably a contradiction? *)
        cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply orutt_Ret.
      unfold_dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp; inv H1.
      unfold_dvalue_refine_strict.
      break_match_goal.
      2: {
        (* Contradiction *)
        exfalso.
        cbn in H2.
        inv H2.
      }

      cbn in *.
      inv H2; inv Heqs0.
      reflexivity.
  Qed.

  Lemma lift_err_uvalue_to_dvalue_orutt_strict_exp_E :
    forall uv1 uv2,
      uvalue_refine_strict uv1 uv2 ->
      orutt exp_E_refine_strict exp_E_res_refine_strict dvalue_refine_strict
        (LLVMEvents.lift_err (fun x : IS1.LP.Events.DV.dvalue => Ret x) (IS1.LP.Events.DV.uvalue_to_dvalue uv1))
        (LLVMEvents.lift_err (fun x : dvalue => Ret x) (uvalue_to_dvalue uv2))
        (OOM:=OOME).
  Proof.
    intros uv1 uv2 H.
    destruct uv1; cbn in *;
      try solve
        [ unfold_uvalue_refine_strict_in H;
          cbn in *; inv H; cbn;
          apply orutt_Ret;
          unfold_dvalue_refine_strict_goal; reflexivity
        | unfold_uvalue_refine_strict_in H;
          cbn in *; inv H; cbn;
          apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; cbn; auto
          ]
        | unfold_uvalue_refine_strict_in H;
          cbn in *;
          break_match_hyp; inv H;
          break_match_hyp; inv H1;
          cbn;
          apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ]
        | unfold_uvalue_refine_strict;
          cbn in *;
          break_match_hyp; inv H;
          cbn;
          apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ]
        | unfold_uvalue_refine_strict;
          cbn in *;
          break_match_hyp; inv H;
          break_match_hyp; inv H1;
          break_match_hyp; inv H0;
          cbn;
          apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ]
        ].
    - unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.
      cbn.
      apply orutt_Ret.
      unfold_dvalue_refine_strict_goal.
      rewrite Heqo.
      cbn.
      reflexivity.
    - unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.
      cbn.
      apply orutt_Ret.
      unfold_dvalue_refine_strict_goal.
      cbn.
      rewrite Heqo.
      reflexivity.
    - (* Structs *)
      unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.

      assert (uvalue_refine_strict (DV1.UVALUE_Struct fields) (DV2.UVALUE_Struct l)) as REF.
      { unfold_uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp; inv H.

        cbn.
        apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ].
      }

      cbn.
      break_match_goal.
      { (* Probably a contradiction? *)
        cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply orutt_Ret.
      unfold_dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp; inv H1.
      unfold_dvalue_refine_strict.
      break_match_goal.
      2: {
        (* Contradiction *)
        exfalso.
        cbn in H2.
        inv H2.
      }

      cbn in *.
      inv H2; inv Heqs0.
      reflexivity.
    - (* Packed Structs *)
      unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.

      assert (uvalue_refine_strict (DV1.UVALUE_Struct fields) (DV2.UVALUE_Struct l)) as REF.
      { unfold_uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp; inv H.

        cbn.
        apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ].
      }

      cbn.
      break_match_goal.
      { (* Probably a contradiction? *)
        cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply orutt_Ret.
      unfold_dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp; inv H1.
      unfold_dvalue_refine_strict.
      break_match_goal.
      2: {
        (* Contradiction *)
        exfalso.
        cbn in H2.
        inv H2.
      }

      cbn in *.
      inv H2; inv Heqs0.
      reflexivity.
    - (* Arrays *)
      unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.

      assert (uvalue_refine_strict (DV1.UVALUE_Array t elts) (DV2.UVALUE_Array t l)) as REF.
      { unfold_uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp; inv H.

        cbn.
        apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ].
      }

      cbn.
      break_match_goal.
      { (* Probably a contradiction? *)
        cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply orutt_Ret.
      unfold_dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp; inv H1.
      unfold_dvalue_refine_strict.
      break_match_goal.
      2: {
        (* Contradiction *)
        exfalso.
        cbn in H2.
        inv H2.
      }

      cbn in *.
      inv H2; inv Heqs0.
      reflexivity.
    - (* Vectors *)
      unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.

      assert (uvalue_refine_strict (DV1.UVALUE_Array t elts) (DV2.UVALUE_Array t l)) as REF.
      { unfold_uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp; inv H.

        cbn.
        apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ].
      }

      cbn.
      break_match_goal.
      { (* Probably a contradiction? *)
        cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply orutt_Ret.
      unfold_dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp; inv H1.
      unfold_dvalue_refine_strict.
      break_match_goal.
      2: {
        (* Contradiction *)
        exfalso.
        cbn in H2.
        inv H2.
      }

      cbn in *.
      inv H2; inv Heqs0.
      reflexivity.
  Qed.

  Lemma lift_err_uvalue_to_dvalue_orutt_strict_L0' :
    forall uv1 uv2,
      uvalue_refine_strict uv1 uv2 ->
      orutt  L0'_refine_strict L0'_res_refine_strict dvalue_refine_strict
        (LLVMEvents.lift_err (fun x : IS1.LP.Events.DV.dvalue => Ret x) (IS1.LP.Events.DV.uvalue_to_dvalue uv1))
        (LLVMEvents.lift_err (fun x : dvalue => Ret x) (uvalue_to_dvalue uv2))
        (OOM:=OOME).
  Proof.
    intros uv1 uv2 H.
    destruct uv1; cbn in *;
      try solve
        [ unfold_uvalue_refine_strict_in H;
          cbn in *; inv H; cbn;
          apply orutt_Ret;
          unfold_dvalue_refine_strict_goal; reflexivity
        | unfold_uvalue_refine_strict_in H;
          cbn in *; inv H; cbn;
          apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; cbn; auto
          ]
        | unfold_uvalue_refine_strict_in H;
          cbn in *;
          break_match_hyp; inv H;
          break_match_hyp; inv H1;
          cbn;
          apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ]
        | unfold_uvalue_refine_strict;
          cbn in *;
          break_match_hyp; inv H;
          cbn;
          apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ]
        | unfold_uvalue_refine_strict;
          cbn in *;
          break_match_hyp; inv H;
          break_match_hyp; inv H1;
          break_match_hyp; inv H0;
          cbn;
          apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ]
        ].
    - unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.
      cbn.
      apply orutt_Ret.
      unfold_dvalue_refine_strict_goal.
      rewrite Heqo.
      cbn.
      reflexivity.
    - unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.
      cbn.
      apply orutt_Ret.
      unfold_dvalue_refine_strict_goal.
      cbn.
      rewrite Heqo.
      reflexivity.
    - (* Structs *)
      unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.

      assert (uvalue_refine_strict (DV1.UVALUE_Struct fields) (DV2.UVALUE_Struct l)) as REF.
      { unfold_uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp; inv H.

        cbn.
        apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ].
      }

      cbn.
      break_match_goal.
      { (* Probably a contradiction? *)
        cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply orutt_Ret.
      unfold_dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp; inv H1.
      unfold_dvalue_refine_strict.
      break_match_goal.
      2: {
        (* Contradiction *)
        exfalso.
        cbn in H2.
        inv H2.
      }

      cbn in *.
      inv H2; inv Heqs0.
      reflexivity.
    - (* Packed Structs *)
      unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.

      assert (uvalue_refine_strict (DV1.UVALUE_Struct fields) (DV2.UVALUE_Struct l)) as REF.
      { unfold_uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp; inv H.

        cbn.
        apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ].
      }

      cbn.
      break_match_goal.
      { (* Probably a contradiction? *)
        cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply orutt_Ret.
      unfold_dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp; inv H1.
      unfold_dvalue_refine_strict.
      break_match_goal.
      2: {
        (* Contradiction *)
        exfalso.
        cbn in H2.
        inv H2.
      }

      cbn in *.
      inv H2; inv Heqs0.
      reflexivity.
    - (* Arrays *)
      unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.

      assert (uvalue_refine_strict (DV1.UVALUE_Array t elts) (DV2.UVALUE_Array t l)) as REF.
      { unfold_uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp; inv H.

        cbn.
        apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ].
      }

      cbn.
      break_match_goal.
      { (* Probably a contradiction? *)
        cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply orutt_Ret.
      unfold_dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp; inv H1.
      unfold_dvalue_refine_strict.
      break_match_goal.
      2: {
        (* Contradiction *)
        exfalso.
        cbn in H2.
        inv H2.
      }

      cbn in *.
      inv H2; inv Heqs0.
      reflexivity.
    - (* Vectors *)
      unfold_uvalue_refine_strict_in H.
      cbn in *.
      break_match_hyp; inv H.

      assert (uvalue_refine_strict (DV1.UVALUE_Array t elts) (DV2.UVALUE_Array t l)) as REF.
      { unfold_uvalue_refine_strict.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      break_match_goal.
      { cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict_error _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [s' H].
        break_match_hyp; inv H.

        cbn.
        apply orutt_raise;
          [ intros msg o CONTRA; inv CONTRA
          | constructor; constructor; cbn; auto
          ].
      }

      cbn.
      break_match_goal.
      { (* Probably a contradiction? *)
        cbn.
        epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        destruct H as [dv2 H].
        rewrite Heqs0 in H.
        destruct H as [CONTRA _].
        inv CONTRA.
      }

      cbn.
      apply orutt_Ret.
      unfold_dvalue_refine_strict.
      cbn.

      epose proof uvalue_to_dvalue_dvalue_refine_strict _ _ _ REF.
      cbn in *.
      rewrite Heqs in H.
      forward H. reflexivity.
      destruct H as [dv2 [H1 H2]].
      break_match_hyp; inv H1.
      unfold_dvalue_refine_strict.
      break_match_goal.
      2: {
        (* Contradiction *)
        exfalso.
        cbn in H2.
        inv H2.
      }

      cbn in *.
      inv H2; inv Heqs0.
      reflexivity.
  Qed.

  Lemma pickUnique_orutt_strict :
    forall uv1 uv2,
      uvalue_refine_strict uv1 uv2 ->
      orutt (sum_prerel call_refine_strict event_refine_strict)
        (sum_postrel call_res_refine_strict event_res_refine_strict) dvalue_refine_strict
        (IS1.LLVM.D.pickUnique uv1) (pickUnique uv2)
        (OOM:=OOME).
  Proof.
    intros uv1 uv2 REF.
    unfold IS1.LLVM.D.pickUnique, IS1.LLVM.D.concretize_or_pick.
    unfold pickUnique, concretize_or_pick.
    cbn.
    break_match;
      eapply uvalue_refine_strict_preserves_is_concrete with (uvc:=uv2) in Heqb; eauto;
      rewrite Heqb.

    apply lift_err_uvalue_to_dvalue_orutt_strict; auto.

    repeat rewrite bind_trigger.
    apply orutt_Vis.

    { constructor.
      cbn; auto.
    }

    intros t1 t2 H.
    apply orutt_Ret.
    destruct t1 as [dv1 []].
    destruct t2 as [dv2 []].
    cbn in *.
    inv H; subst_existT; cbn in *.
    tauto.

    intros o CONTRA; inv CONTRA.
  Qed.

  (* TODO: can these pickUnique lemmas be generalized? Different
  prerel / postrel, but fundamentally the same lemma... *)
  Lemma pickUnique_instr_E_orutt_strict :
    forall uv1 uv2,
      uvalue_refine_strict uv1 uv2 ->
      orutt instr_E_refine_strict instr_E_res_refine_strict dvalue_refine_strict
        (IS1.LLVM.D.pickUnique uv1) (pickUnique uv2)
        (OOM:=OOME).
  Proof.
    intros uv1 uv2 REF.
    unfold IS1.LLVM.D.pickUnique, IS1.LLVM.D.concretize_or_pick.
    unfold pickUnique, concretize_or_pick.
    cbn.
    break_match;
      eapply uvalue_refine_strict_preserves_is_concrete with (uvc:=uv2) in Heqb; eauto;
      rewrite Heqb.

    apply lift_err_uvalue_to_dvalue_orutt_strict_instr_E; eauto.

    repeat rewrite bind_trigger.
    apply orutt_Vis.

    { cbn; auto.
    }

    intros t1 t2 H.
    apply orutt_Ret.
    destruct t1 as [dv1 []].
    destruct t2 as [dv2 []].
    cbn in *.
    inv H; subst_existT; cbn in *.
    tauto.

    intros o CONTRA; inv CONTRA.
  Qed.

  Lemma pickUnique_exp_E_orutt_strict :
    forall uv1 uv2,
      uvalue_refine_strict uv1 uv2 ->
      orutt exp_E_refine_strict exp_E_res_refine_strict dvalue_refine_strict
        (IS1.LLVM.D.pickUnique uv1) (pickUnique uv2)
        (OOM:=OOME).
  Proof.
    intros uv1 uv2 REF.
    unfold IS1.LLVM.D.pickUnique, IS1.LLVM.D.concretize_or_pick.
    unfold pickUnique, concretize_or_pick.
    cbn.
    break_match;
      eapply uvalue_refine_strict_preserves_is_concrete with (uvc:=uv2) in Heqb; eauto;
      rewrite Heqb.

    apply lift_err_uvalue_to_dvalue_orutt_strict_exp_E; eauto.

    repeat rewrite bind_trigger.
    apply orutt_Vis.

    { cbn; auto. }

    intros t1 t2 H.
    apply orutt_Ret.
    destruct t1 as [dv1 []].
    destruct t2 as [dv2 []].
    cbn in *.
    inv H; subst_existT; cbn in *.
    tauto.

    intros o CONTRA; inv CONTRA.
  Qed.

  Lemma orutt_eval_iop :
    forall iop dv1_1 dv2_1 dv1_2 dv2_2,
      dvalue_refine_strict dv1_1 dv1_2 ->
      dvalue_refine_strict dv2_1 dv2_2 ->
      orutt exp_E_refine_strict exp_E_res_refine_strict dvalue_refine_strict
        (IS1.LP.Events.DV.eval_iop iop dv1_1 dv2_1) (eval_iop iop dv1_2 dv2_2)
        (OOM:=OOME).
  Proof.
    intros iop dv1_1 dv2_1 dv1_2 dv2_2 H H0.
    rewrite eval_iop_err_ub_oom_to_itree,
      TLR1.eval_iop_err_ub_oom_to_itree.

    remember (eval_iop iop dv1_2 dv2_2) as e.
    destruct_err_ub_oom e; symmetry in Heqe.
    - apply orutt_raiseOOM.
    - erewrite eval_iop_ub_fin_inf; cbn; eauto;
        try erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
      apply orutt_raiseUB; cbn; auto.
      intros ? ? CONTRA.
      inv CONTRA.
    - erewrite eval_iop_err_fin_inf; cbn; eauto;
        try erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
      apply orutt_raise; cbn; auto.
      intros ? ? CONTRA.
      inv CONTRA.
    - erewrite eval_iop_fin_inf; cbn; eauto; subst.
      2-3: try erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
      apply orutt_Ret; cbn; eauto.
      apply fin_to_inf_dvalue_refine_strict.
  Qed.

  Lemma orutt_eval_icmp :
    forall cmp dv1_1 dv2_1 dv1_2 dv2_2,
      dvalue_refine_strict dv1_1 dv1_2 ->
      dvalue_refine_strict dv2_1 dv2_2 ->
      orutt exp_E_refine_strict exp_E_res_refine_strict dvalue_refine_strict
        (IS1.MEM.CP.CONC.eval_icmp cmp dv1_1 dv2_1) (eval_icmp cmp dv1_2 dv2_2)
        (OOM:=OOME).
  Proof.
    intros cmp dv1_1 dv2_1 dv1_2 dv2_2 H H0.
    rewrite eval_icmp_err_ub_oom_to_itree,
      TLR1.eval_icmp_err_ub_oom_to_itree.

    remember (eval_icmp cmp dv1_2 dv2_2) as e.
    destruct_err_ub_oom e; symmetry in Heqe.
    - apply orutt_raiseOOM.
    - erewrite eval_icmp_ub_fin_inf; cbn; eauto;
        try erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
      apply orutt_raiseUB; cbn; auto.
      intros ? ? CONTRA.
      inv CONTRA.
    - erewrite eval_icmp_err_fin_inf; cbn; eauto;
        try erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
      apply orutt_raise; cbn; auto.
      intros ? ? CONTRA.
      inv CONTRA.
    - erewrite eval_icmp_fin_inf; cbn; eauto; subst.
      2-3: try erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
      apply orutt_Ret; cbn; eauto.
      apply fin_to_inf_dvalue_refine_strict.
  Qed.

  Lemma orutt_eval_fop :
    forall fop dv1_1 dv2_1 dv1_2 dv2_2,
      dvalue_refine_strict dv1_1 dv1_2 ->
      dvalue_refine_strict dv2_1 dv2_2 ->
      orutt exp_E_refine_strict exp_E_res_refine_strict dvalue_refine_strict
        (IS1.LP.Events.DV.eval_fop fop dv1_1 dv2_1) (eval_fop fop dv1_2 dv2_2)
        (OOM:=OOME).
  Proof.
    intros fop dv1_1 dv2_1 dv1_2 dv2_2 H H0.
    rewrite eval_fop_err_ub_oom_to_itree,
      TLR1.eval_fop_err_ub_oom_to_itree.

    remember (eval_fop fop dv1_2 dv2_2) as e.
    destruct_err_ub_oom e; symmetry in Heqe.
    - apply orutt_raiseOOM.
    - erewrite eval_fop_ub_fin_inf; cbn; eauto;
        try erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
      apply orutt_raiseUB; cbn; auto.
      intros ? ? CONTRA.
      inv CONTRA.
    - erewrite eval_fop_err_fin_inf; cbn; eauto;
        try erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
      apply orutt_raise; cbn; auto.
      intros ? ? CONTRA.
      inv CONTRA.
    - erewrite eval_fop_fin_inf; cbn; eauto; subst.
      2-3: try erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
      apply orutt_Ret; cbn; eauto.
      apply fin_to_inf_dvalue_refine_strict.
  Qed.

  Lemma orutt_eval_fcmp :
    forall cmp dv1_1 dv2_1 dv1_2 dv2_2,
      dvalue_refine_strict dv1_1 dv1_2 ->
      dvalue_refine_strict dv2_1 dv2_2 ->
      orutt exp_E_refine_strict exp_E_res_refine_strict dvalue_refine_strict
        (IS1.LP.Events.DV.eval_fcmp cmp dv1_1 dv2_1) (eval_fcmp cmp dv1_2 dv2_2)
        (OOM:=OOME).
  Proof.
    intros cmp dv1_1 dv2_1 dv1_2 dv2_2 H H0.
    rewrite eval_fcmp_err_ub_oom_to_itree,
      TLR1.eval_fcmp_err_ub_oom_to_itree.

    remember (eval_fcmp cmp dv1_2 dv2_2) as e.
    destruct_err_ub_oom e; symmetry in Heqe.
    - apply orutt_raiseOOM.
    - erewrite eval_fcmp_ub_fin_inf; cbn; eauto;
        try erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
      apply orutt_raiseUB; cbn; auto.
      intros ? ? CONTRA.
      inv CONTRA.
    - erewrite eval_fcmp_err_fin_inf; cbn; eauto;
        try erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
      apply orutt_raise; cbn; auto.
      intros ? ? CONTRA.
      inv CONTRA.
    - erewrite eval_fcmp_fin_inf; cbn; eauto; subst.
      2-3: try erewrite <- fin_to_inf_dvalue_refine_strict'; eauto.
      apply orutt_Ret; cbn; eauto.
      apply fin_to_inf_dvalue_refine_strict.
  Qed.

  Lemma fin_to_inf_dvalue_dvalue_int_unsigned :
    forall dv,
      IS1.LP.Events.DV.dvalue_int_unsigned (fin_to_inf_dvalue dv) = dvalue_int_unsigned dv.
  Proof.
    intros dv.
    destruct dv; cbn;
      rewrite_fin_to_inf_dvalue;
      cbn;
      auto.

    unfold intptr_fin_inf.
    break_match; clear Heqs.
    apply IS1.LP.IP.from_Z_to_Z in e.
    rewrite <- IP.to_Z_to_unsigned.
    rewrite <- IS1.LP.IP.to_Z_to_unsigned.
    auto.
  Qed.

  (* TODO: Move this *)
  Lemma uvalue_strict_subterm_gep_cons :
    forall τ1 τ2 u uv_addr uv_idx uv_idxs,
      uvalue_strict_subterm u (UVALUE_GetElementPtr τ1 uv_addr uv_idxs) ->
      uvalue_strict_subterm u (UVALUE_GetElementPtr τ2 uv_addr (uv_idx :: uv_idxs)).
  Proof.
    intros τ1 τ2 u uv_addr uv_idx uv_idxs H.
    dependent induction H.
    - inv H.
      repeat constructor.
      eapply uvalue_getelementptr_strict_subterm.
      apply Exists_In.
      exists x.
      split; cbn; auto.
      apply rt_refl.
    - specialize (IHclos_trans2 τ1 uv_addr uv_idxs eq_refl).
      eapply t_trans.
      apply H.
      apply IHclos_trans2.
  Qed.

  (* TODO: Move this *)
  Lemma addr_convert_safe_reverse :
    forall a1 a2,
      AC1.addr_convert a1 = NoOom a2 ->
      AC2.addr_convert a2 = NoOom a1.
  Proof.
    intros a1 a2 H.
    pose proof addr_refine_fin_to_inf_addr a2 as REF.
    red in REF.
    unfold fin_to_inf_addr in REF.
    break_match_hyp.
    clear Heqs.
    rewrite e.
    pose proof (AC1.addr_convert_injective _ _ _ H REF); subst; auto.
  Qed.

  (* TODO: Move this *)
  Lemma orutt_index_into_vec_dv :
    forall τ dv1_1 dv2_1 dv1_2 dv2_2,
      dvalue_refine_strict dv1_1 dv1_2 ->
      dvalue_refine_strict dv2_1 dv2_2 ->
      orutt exp_E_refine_strict exp_E_res_refine_strict dvalue_refine_strict
        (IS1.LP.Events.DV.index_into_vec_dv τ dv1_1 dv2_1) (index_into_vec_dv τ dv1_2 dv2_2)
        (OOM:=OOME).
  Proof.
    intros τ dv1_1 dv2_1 dv1_2 dv2_2 REF1 REF2.
    rewrite TLR1.index_into_vec_dv_err_ub_oom_to_itree,
      TLR2.index_into_vec_dv_err_ub_oom_to_itree.

    erewrite (fin_to_inf_dvalue_refine_strict' dv1_1); eauto.
    erewrite (fin_to_inf_dvalue_refine_strict' dv2_1); eauto.

    remember (index_into_vec_dv τ dv1_2 dv2_2) as res.
    destruct_err_ub_oom res;
      symmetry in Heqres.
    - apply orutt_raiseOOM.
    - apply index_into_vec_dv_no_ub in Heqres; contradiction.
    - erewrite index_into_vec_dv_err_fin_inf; eauto.
      apply orutt_raise;
        [ intros ? ? CONTRA; inv CONTRA | cbn; auto ].
    - erewrite index_into_vec_dv_fin_inf; cbn; eauto.
      apply orutt_Ret.
      apply fin_to_inf_dvalue_refine_strict.
  Qed.

  (* TODO: Move this *)
  Lemma orutt_insert_into_vec_dv :
    forall τ dv1_1 dv2_1 dv3_1 dv1_2 dv2_2 dv3_2,
      dvalue_refine_strict dv1_1 dv1_2 ->
      dvalue_refine_strict dv2_1 dv2_2 ->
      dvalue_refine_strict dv3_1 dv3_2 ->
      orutt exp_E_refine_strict exp_E_res_refine_strict dvalue_refine_strict
        (IS1.LP.Events.DV.insert_into_vec_dv τ dv1_1 dv2_1 dv3_1) (insert_into_vec_dv τ dv1_2 dv2_2 dv3_2)
        (OOM:=OOME).
  Proof.
    intros τ dv1_1 dv2_1 dv3_1 dv1_2 dv2_2 dv3_2 REF1 REF2 REF3.
    rewrite TLR1.insert_into_vec_dv_err_ub_oom_to_itree,
      TLR2.insert_into_vec_dv_err_ub_oom_to_itree.

    erewrite (fin_to_inf_dvalue_refine_strict' dv1_1); eauto.
    erewrite (fin_to_inf_dvalue_refine_strict' dv2_1); eauto.
    erewrite (fin_to_inf_dvalue_refine_strict' dv3_1); eauto.

    remember (insert_into_vec_dv τ dv1_2 dv2_2 dv3_2) as res.
    destruct_err_ub_oom res;
      symmetry in Heqres.
    - apply orutt_raiseOOM.
    - apply insert_into_vec_dv_no_ub_fin_inf in Heqres; contradiction.
    - erewrite insert_into_vec_dv_err_fin_inf; eauto.
      apply orutt_raise;
        [ intros ? ? CONTRA; inv CONTRA | cbn; auto ].
    - erewrite insert_into_vec_dv_fin_inf; cbn; eauto.
      apply orutt_Ret.
      apply fin_to_inf_dvalue_refine_strict.
  Qed.

  Lemma dvalue_refine_strict_map_fin_to_inf_dvalue :
    forall a b,
      Forall2 dvalue_refine_strict a b ->
      a = map fin_to_inf_dvalue b.
  Proof.
    intros a b H.
    induction H; cbn; auto.

    subst.
    unfold fin_to_inf_dvalue at 2.
    break_match; clear Heqs.
    destruct p.
    red in H.
    pose proof dvalue_refine_strict_R2_injective x y x0 y H e0 as (_&?).
    rewrite H1; auto.
  Qed.

  (* TODO: Move this *)
  Lemma extract_value_loop_fin_inf_no_ub :
    forall idxs str msg,
      (fix loop str idxs {struct idxs} : err_ub_oom dvalue :=
         match idxs with
         | [] => ret str
         | i :: tl =>
             v <- index_into_str_dv str i ;;
             loop v tl
         end) str idxs = UB_unERR_UB_OOM msg -> False.
  Proof.
    induction idxs;
      intros str res LOOP.
    - inv LOOP; auto.
    - cbn in LOOP.
      repeat break_match_hyp_inv.
      destruct unERR_UB_OOM, unEitherT, unEitherT, unEitherT, unIdent;
        inv Heqs.
      + apply index_into_str_dv_no_ub_fin_inf in Heqe; auto.
      + match goal with
        | H: EitherMonad.unEitherT
               (EitherMonad.unEitherT
                  (EitherMonad.unEitherT
                     (Error.unERR_UB_OOM
                        (?L)))) = _ |- _ =>
            remember L as LOOP
        end.

        destruct_err_ub_oom LOOP; inv H1.
        symmetry in HeqLOOP.
        apply IHidxs in HeqLOOP; auto.
  Qed.

  (* TODO: Move this *)
  Lemma orutt_extractvalue_loop :
    forall dv1 dv2 idxs,
      dvalue_refine_strict dv1 dv2 ->
      orutt exp_E_refine_strict exp_E_res_refine_strict dvalue_refine_strict
        ((fix loop (str : IS1.LP.Events.DV.dvalue) (idxs0 : list LLVMAst.int_ast) {struct idxs0} :
           itree IS1.LP.Events.exp_E IS1.LP.Events.DV.dvalue :=
            match idxs0 with
            | [] => Ret str
            | i :: tl =>
                ITree.bind (IS1.LP.Events.DV.index_into_str_dv str i)
                  (fun v : IS1.LP.Events.DV.dvalue => loop v tl)
            end) dv1 idxs)
        ((fix loop (str : dvalue) (idxs0 : list LLVMAst.int_ast) {struct idxs0} : itree exp_E dvalue :=
            match idxs0 with
            | [] => Ret str
            | i :: tl => ITree.bind (index_into_str_dv str i) (fun v : dvalue => loop v tl)
            end) dv2 idxs)
        (OOM:=OOME).
  Proof.
    intros dv1 dv2 idxs REF.
    setoid_rewrite TLR1.extract_value_loop_err_ub_oom_to_itree;
      setoid_rewrite TLR2.extract_value_loop_err_ub_oom_to_itree.

    erewrite (fin_to_inf_dvalue_refine_strict' dv1); eauto.

    remember
      ((fix loop (str : dvalue) (idxs0 : list LLVMAst.int_ast) {struct idxs0} : err_ub_oom dvalue :=
          match idxs0 with
          | [] => ret str
          | i :: tl => v <- index_into_str_dv str i;; loop v tl
          end) dv2 idxs) as res.
    destruct_err_ub_oom res;
      symmetry in Heqres.
    - apply orutt_raiseOOM.
    - apply extract_value_loop_fin_inf_no_ub in Heqres; contradiction.
    - erewrite extract_value_loop_fin_inf_err; eauto.
      apply orutt_raise;
        [ intros ? ? CONTRA; inv CONTRA | cbn; auto ].
    - erewrite extract_value_loop_fin_inf_succeeds; cbn; eauto.
      apply orutt_Ret.
      apply fin_to_inf_dvalue_refine_strict.
  Qed.

  Lemma orutt_insert_value_loop :
    forall dv1 dv2 dv1' dv2' idxs,
      dvalue_refine_strict dv1 dv2 ->
      dvalue_refine_strict dv1' dv2' ->
      orutt exp_E_refine_strict exp_E_res_refine_strict dvalue_refine_strict
        ((fix loop (str : IS1.LP.Events.DV.dvalue) (idxs0 : list LLVMAst.int_ast) {struct idxs0} :
           itree IS1.LP.Events.exp_E IS1.LP.Events.DV.dvalue :=
            match idxs0 with
            | [] => LLVMEvents.raise "Index was not provided"
            | [i] =>
                ITree.bind (IS1.LP.Events.DV.insert_into_str str dv1' i)
                  (fun v : IS1.LP.Events.DV.dvalue => Ret v)
            | i :: (_ :: _) as tl =>
                ITree.bind (IS1.LP.Events.DV.index_into_str_dv str i)
                  (fun subfield : IS1.LP.Events.DV.dvalue =>
                     ITree.bind (loop subfield tl)
                       (fun modified_subfield : IS1.LP.Events.DV.dvalue =>
                          IS1.LP.Events.DV.insert_into_str str modified_subfield i))
            end) dv1 idxs)
        ((fix loop (str : dvalue) (idxs0 : list LLVMAst.int_ast) {struct idxs0} : itree exp_E dvalue :=
            match idxs0 with
            | [] => LLVMEvents.raise "Index was not provided"
            | [i] => ITree.bind (insert_into_str str dv2' i) (fun v : dvalue => Ret v)
            | i :: (_ :: _) as tl =>
                ITree.bind (index_into_str_dv str i)
                  (fun subfield : dvalue =>
                     ITree.bind (loop subfield tl)
                       (fun modified_subfield : dvalue => insert_into_str str modified_subfield i))
            end) dv2 idxs)
        (OOM:=OOME).
  Proof.
    intros dv1 dv2 dv1' dv2' idxs REF1 REF2.
    setoid_rewrite TLR1.insert_value_loop_err_ub_oom_to_itree;
      setoid_rewrite TLR2.insert_value_loop_err_ub_oom_to_itree.

    erewrite (fin_to_inf_dvalue_refine_strict' dv1); eauto.
    erewrite (fin_to_inf_dvalue_refine_strict' dv1'); eauto.

    erewrite insert_value_loop_fin_inf_succeeds; eauto.
    remember
      ((fix loop (str : dvalue) (idxs0 : list LLVMAst.int_ast) {struct idxs0} : err_ub_oom dvalue :=
          match idxs0 with
          | [] => raise_error "Index was not provided"
          | [i] => v <- insert_into_str str dv2' i;; ret v
          | i :: (_ :: _) as tl =>
              subfield <- index_into_str_dv str i;;
              modified_subfield <- loop subfield tl;; insert_into_str str modified_subfield i
          end) dv2 idxs) as res.
    destruct_err_ub_oom res;
      symmetry in Heqres; cbn.
    - apply orutt_raiseOOM.
    - apply orutt_raiseUB;
        [ intros ? ? CONTRA; inv CONTRA | cbn; auto ].
    - apply orutt_raise;
        [ intros ? ? CONTRA; inv CONTRA | cbn; auto ].
    - apply orutt_Ret.
      apply fin_to_inf_dvalue_refine_strict.
  Qed.

  Lemma orutt_dvalue_bytes_to_dvalue :
    forall dt (r1 : list IS1.MEM.DVALUE_BYTE.dvalue_byte) (r2 : list dvalue_byte),
      dvalue_bytes_refine r1 r2 ->
      orutt (OOM:=OOME) exp_E_refine_strict exp_E_res_refine_strict dvalue_refine_strict
        (ErrOOMPoison_handle_poison_and_oom IS1.LP.Events.DV.DVALUE_Poison
           (IS1.LLVM.MEM.MP.DVALUE_BYTES.dvalue_bytes_to_dvalue r1 dt))
        (ErrOOMPoison_handle_poison_and_oom DVALUE_Poison (DVALUE_BYTES.dvalue_bytes_to_dvalue r2 dt)).
  Proof.
    intros ? ? ? ?.
    rewrite TLR1.handle_poison_and_oom_dvalue_bytes_to_dvalue_err_ub_oom_to_itree,
      TLR2.handle_poison_and_oom_dvalue_bytes_to_dvalue_err_ub_oom_to_itree.
    remember (ErrOOMPoison_handle_poison_and_oom DVALUE_Poison (DVALUE_BYTES.dvalue_bytes_to_dvalue r2 dt)) as res.
    destruct_err_ub_oom res; symmetry in Heqres.
    - apply orutt_raiseOOM.
    - erewrite dvalue_bytes_to_dvalue_ub_fin_inf; eauto.
      apply orutt_raiseUB;
        [ intros ? ? CONTRA; inv CONTRA | cbn; auto ].
    - erewrite dvalue_bytes_to_dvalue_err_fin_inf; eauto.
      apply orutt_raise;
        [ intros ? ? CONTRA; inv CONTRA | cbn; auto ].
    - erewrite dvalue_bytes_to_dvalue_fin_inf; eauto.
      apply orutt_Ret.
      apply fin_to_inf_dvalue_refine_strict.
  Qed.

  (* TODO: Move this *)
  Lemma orutt_eval_select_loop :
    forall cnds1 xs1 ys1 cnds2 xs2 ys2,
      map_monad dvalue_convert_strict cnds1 = NoOom cnds2 ->
      map_monad dvalue_convert_strict xs1 = NoOom xs2 ->
      map_monad dvalue_convert_strict ys1 = NoOom ys2 ->
      orutt (OOM:=OOME) exp_E_refine_strict exp_E_res_refine_strict (Forall2 dvalue_refine_strict)
        ((fix loop (conds xs ys : list IS1.LP.Events.DV.dvalue) {struct conds} :
           itree IS1.LP.Events.exp_E (list IS1.LP.Events.DV.dvalue) :=
            match conds with
            | [] =>
                match xs with
                | [] =>
                    fun ys0 : list IS1.LP.Events.DV.dvalue =>
                      match ys0 with
                      | [] => Ret []
                      | _ :: _ =>
                          LLVMEvents.raise "concretize_uvalueM: ill-typed vector select, length mismatch."
                      end
                | _ :: _ =>
                    fun _ : list IS1.LP.Events.DV.dvalue =>
                      LLVMEvents.raise "concretize_uvalueM: ill-typed vector select, length mismatch."
                end ys
            | c :: conds0 =>
                match xs with
                | [] => LLVMEvents.raise "concretize_uvalueM: ill-typed vector select, length mismatch."
                | x5 :: xs0 =>
                    match ys with
                    | [] =>
                        LLVMEvents.raise "concretize_uvalueM: ill-typed vector select, length mismatch."
                    | y :: ys0 =>
                        ITree.bind
                          match c with
                          | @IS1.LP.Events.DV.DVALUE_I 1 i =>
                              if (@Integers.unsigned 1 i =? 1)%Z then Ret x5 else Ret y
                          | IS1.LP.Events.DV.DVALUE_Poison t => Ret (IS1.LP.Events.DV.DVALUE_Poison t)
                          | _ =>
                              LLVMEvents.raise
                                "concretize_uvalueM: ill-typed select, condition in vector was not poison or i1."
                          end
                          (fun selected : IS1.LP.Events.DV.dvalue =>
                             ITree.bind (loop conds0 xs0 ys0)
                               (fun rest : list IS1.LP.Events.DV.dvalue => Ret (selected :: rest)))
                    end
                end
            end) cnds1 xs1 ys1)
        ((fix loop (conds xs ys : list dvalue) {struct conds} : itree exp_E (list dvalue) :=
            match conds with
            | [] =>
                match xs with
                | [] =>
                    fun ys0 : list dvalue =>
                      match ys0 with
                      | [] => Ret []
                      | _ :: _ =>
                          LLVMEvents.raise "concretize_uvalueM: ill-typed vector select, length mismatch."
                      end
                | _ :: _ =>
                    fun _ : list dvalue =>
                      LLVMEvents.raise "concretize_uvalueM: ill-typed vector select, length mismatch."
                end ys
            | c :: conds0 =>
                match xs with
                | [] => LLVMEvents.raise "concretize_uvalueM: ill-typed vector select, length mismatch."
                | x5 :: xs0 =>
                    match ys with
                    | [] =>
                        LLVMEvents.raise "concretize_uvalueM: ill-typed vector select, length mismatch."
                    | y :: ys0 =>
                        ITree.bind
                          match c with
                          | @DVALUE_I 1 i => if (@Integers.unsigned 1 i =? 1)%Z then Ret x5 else Ret y
                          | DVALUE_Poison t => Ret (DVALUE_Poison t)
                          | _ =>
                              LLVMEvents.raise
                                "concretize_uvalueM: ill-typed select, condition in vector was not poison or i1."
                          end
                          (fun selected : dvalue =>
                             ITree.bind (loop conds0 xs0 ys0)
                               (fun rest : list dvalue => Ret (selected :: rest)))
                    end
                end
            end) cnds2 xs2 ys2).
  Proof.
    intros cnds1.

    induction cnds1, xs1, ys1;
      intros cnds2 xs2 ys2 REF_CNDS REF_XS REF_YS;
      cbn in *; subst; inv REF_CNDS; inv REF_XS; inv REF_YS;
      repeat break_match_hyp_inv; cbn;
      try solve
        [ apply orutt_raise;
          [ intros ? ? CONTRA; inv CONTRA | cbn; auto ]
        ].

    apply orutt_Ret; constructor.

    specialize (IHcnds1 xs1 ys1 l1 l0 l eq_refl Heqo2 Heqo0).
    eapply orutt_bind with (RR:=dvalue_refine_strict).
    { destruct d3;
        dvalue_convert_strict_inv Heqo3; cbn;
        try solve
          [ repeat break_match; (apply orutt_raise;
            [ intros ? ? CONTRA; inv CONTRA | cbn; auto ])
          ].
      - repeat break_match; try (apply orutt_raise;
            [ intros ? ? CONTRA; inv CONTRA | cbn; auto ]);
          apply orutt_Ret; eauto.
      - apply orutt_Ret; eauto.
        solve_dvalue_refine_strict.
    }

    intros ? ? ?.
    eapply orutt_bind with (RR:=Forall2 dvalue_refine_strict); eauto.
    intros ? ? ?.
    eapply orutt_Ret.
    apply Forall2_cons; eauto.
  Qed.

  Lemma orutt_concretize_uvalue_bytes_helper :
    forall uvs1 uvs2 acc1 acc2
      (IH : forall (uv_fin : DV2.uvalue),
          Exists (DV2.uvalue_subterm uv_fin) uvs2 ->
          forall u : DV1.uvalue,
            uvalue_refine_strict u uv_fin ->
            orutt (OOM:=OOME) exp_E_refine_strict exp_E_res_refine_strict dvalue_refine_strict
              (IS1.LLVM.MEM.CP.CONC.concretize_uvalue u) (concretize_uvalue uv_fin)),
      Forall2 uvalue_refine_strict uvs1 uvs2 ->
      concretization_map_refine acc1 acc2 ->
      orutt (OOM:=OOME) exp_E_refine_strict exp_E_res_refine_strict dvalue_bytes_refine
        ((fix concretize_uvalue_bytes_helper
            (acc : NMap (list (IS1.LP.Events.DV.uvalue * IS1.LP.Events.DV.dvalue)))
            (uvs0 : list IS1.LP.Events.DV.uvalue) {struct uvs0} :
           itree IS1.LP.Events.exp_E (list IS1.LLVM.MEM.MP.DVALUE_BYTES.dvalue_byte) :=
            match uvs0 with
            | [] => Ret []
            | IS1.LP.Events.DV.UVALUE_ExtractByte byte_uv dt0 idx sid :: uvs1 =>
                match
                  match
                    NM.find (elt:=list (IS1.LP.Events.DV.uvalue * IS1.LP.Events.DV.dvalue)) sid acc
                  with
                  | Some v => Util.assoc byte_uv v
                  | None => None
                  end
                with
                | Some dv =>
                    ITree.bind (concretize_uvalue_bytes_helper acc uvs1)
                      (fun rest : list IS1.LLVM.MEM.MP.DVALUE_BYTES.dvalue_byte =>
                         Ret (IS1.LLVM.MEM.MP.DVALUE_BYTES.DVALUE_ExtractByte dv dt0 idx :: rest))
                | None =>
                    ITree.bind
                      (IS1.LLVM.MEM.CP.CONC.concretize_uvalueM (itree IS1.LP.Events.exp_E)
                         (fun dt1 : dtyp =>
                            lift_err_RAISE_ERROR (IS1.LP.Events.DV.default_dvalue_of_dtyp dt1))
                         (itree IS1.LP.Events.exp_E)
                         (fun (A : Type) (x0 : itree IS1.LP.Events.exp_E A) => x0) byte_uv)
                      (fun dv : IS1.LP.Events.DV.dvalue =>
                         ITree.bind
                           (concretize_uvalue_bytes_helper
                              (IS1.LLVM.MEM.CP.CONCBASE.new_concretized_byte acc byte_uv dv sid) uvs1)
                           (fun rest : list IS1.LLVM.MEM.MP.DVALUE_BYTES.dvalue_byte =>
                              Ret (IS1.LLVM.MEM.MP.DVALUE_BYTES.DVALUE_ExtractByte dv dt0 idx :: rest)))
                end
            | _ => LLVMEvents.raise "concretize_uvalue_bytes_helper: non-byte in uvs."
            end) acc1 uvs1)
        ((fix concretize_uvalue_bytes_helper
            (acc : NMap (list (uvalue * dvalue))) (uvs0 : list uvalue) {struct uvs0} :
           itree exp_E (list DVALUE_BYTES.dvalue_byte) :=
            match uvs0 with
            | [] => Ret []
            | UVALUE_ExtractByte byte_uv dt0 idx sid :: uvs1 =>
                match
                  match NM.find (elt:=list (uvalue * dvalue)) sid acc with
                  | Some v => Util.assoc byte_uv v
                  | None => None
                  end
                with
                | Some dv =>
                    ITree.bind (concretize_uvalue_bytes_helper acc uvs1)
                      (fun rest : list DVALUE_BYTES.dvalue_byte =>
                         Ret (DVALUE_BYTES.DVALUE_ExtractByte dv dt0 idx :: rest))
                | None =>
                    ITree.bind
                      (CONC.concretize_uvalueM (itree exp_E)
                         (fun dt1 : dtyp => lift_err_RAISE_ERROR (default_dvalue_of_dtyp dt1))
                         (itree exp_E) (fun (A : Type) (x0 : itree exp_E A) => x0) byte_uv)
                      (fun dv : dvalue =>
                         ITree.bind
                           (concretize_uvalue_bytes_helper (new_concretized_byte acc byte_uv dv sid) uvs1)
                           (fun rest : list DVALUE_BYTES.dvalue_byte =>
                              Ret (DVALUE_BYTES.DVALUE_ExtractByte dv dt0 idx :: rest)))
                end
            | _ => LLVMEvents.raise "concretize_uvalue_bytes_helper: non-byte in uvs."
            end) acc2 uvs2).
  Proof.
    intros uvs1 uvs2 acc1 acc2 IH REF ACC_REF.
    revert acc1 acc2 ACC_REF.
    induction REF; intros acc1 acc2 ACC_REF.
    - apply orutt_Ret.
      constructor.
    - destruct y; uvalue_refine_strict_inv H;
        try solve
          [ apply orutt_raise;
            [ intros ? ? CONTRA; inv CONTRA | cbn; auto ]
          ].
      cbn.
      cbn.

      pose proof ACC_REF as (?&?).
      break_inner_match.
      2: {
        destruct (NM.find (elt:=list (uvalue * dvalue)) sid acc2) eqn:FIND2.
        { exfalso.
          apply NM_find_not_In in Heqo.
          apply Heqo.
          apply H.
          eapply NM_find_In; eauto.
        }

        eapply orutt_bind with (RR:=dvalue_refine_strict).
        { apply IH; auto.
          repeat constructor.
        }

        intros ? ? ?.
        eapply orutt_bind with (RR:=dvalue_bytes_refine).
        eapply IHREF; eauto.
        apply concretize_map_refine_new_concretized_byte_fin_inf; eauto.

        intros ? ? ?.
        apply orutt_Ret.
        red.
        constructor; cbn; eauto.
      }

      eapply concretize_map_refine_find_some_inf_fin in Heqo; eauto.
      destruct Heqo as (?&?&?).
      rewrite H2.
      break_match.
      { eapply assoc_similar_lookup in Heqo.
        2: apply uvalue_refine_strict_R2_injective.
        2: apply H3.

        destruct Heqo as (?&?&?&?&?&?).
        pose proof (Util.Forall2_Nth H5 H6 H3).
        destruct H7.
        cbn in *.
        red in fst_rel.
        setoid_rewrite H0 in fst_rel.
        inv fst_rel.

        subst.
        rewrite H4.

        eapply orutt_bind with (RR:=dvalue_bytes_refine).
        eapply IHREF; auto.

        intros ? ? ?.
        apply orutt_Ret.
        red.
        constructor; cbn; eauto.
      }

      { eapply (assoc_similar_no_lookup uvalue_refine_strict dvalue_refine_strict l0 x) in Heqo.
        2: apply uvalue_refine_strict_R2_injective.
        2: apply H3.
        2: eauto.

        rewrite Heqo.

        eapply orutt_bind with (RR:=dvalue_refine_strict).
        { apply IH; auto.
          repeat constructor.
        }

        intros ? ? ?.
        eapply orutt_bind with (RR:=dvalue_bytes_refine).
        eapply IHREF; eauto.
        apply concretize_map_refine_new_concretized_byte_fin_inf; eauto.

        intros ? ? ?.
        apply orutt_Ret.
        red.
        constructor; cbn; eauto.
      }
  Qed.

  Lemma orutt_concretize_uvalue :
    forall u2 u1,
      uvalue_refine_strict u1 u2 ->
      orutt exp_E_refine_strict exp_E_res_refine_strict dvalue_refine_strict
        (IS1.LLVM.MEM.CP.CONC.concretize_uvalue u1)
        (concretize_uvalue u2)
        (OOM:=OOME).
  Proof.
    intros u2.
    induction u2 using DV2.uvalue_strong_ind; intros u1 REF;
      try DVC.uvalue_refine_strict_inv REF;
      try solve
        [ cbn;
          eapply orutt_Ret;
          rewrite dvalue_refine_strict_equation;
          cbn; try rewrite H; auto
        ].
    - cbn.
      unfold lift_err_RAISE_ERROR.
      cbn.
      break_match.
      + apply DVCrev.default_dvalue_of_dtyp_dv1_dv2_same_error in Heqs.
        rewrite Heqs.
        apply orutt_raise; cbn; auto.
        intros msg o CONTRA.
        inv CONTRA.
      + apply DVC.default_dvalue_of_dtyp_dv1_dv2_equiv in Heqs.
        destruct Heqs as (?&?&?).
        rewrite H.
        apply orutt_Ret; auto.
    - destruct u2;
        try DVC.uvalue_refine_strict_inv REF;
        try solve
          [ cbn;
            eapply orutt_Ret;
            rewrite dvalue_refine_strict_equation;
            cbn; try rewrite H0; auto
          ].
      + cbn.
        unfold lift_err_RAISE_ERROR.
        cbn.
        break_match.
        * apply DVCrev.default_dvalue_of_dtyp_dv1_dv2_same_error in Heqs.
          rewrite Heqs.
          apply orutt_raise; cbn; auto.
          intros msg o CONTRA.
          inv CONTRA.
        * apply DVC.default_dvalue_of_dtyp_dv1_dv2_equiv in Heqs.
          destruct Heqs as (?&?&?).
          rewrite H0.
          apply orutt_Ret; auto.
      + (* Struct *) cbn.
        eapply map_monad_oom_Forall2 in H1.
        assert (Forall2 (fun (a : DV1.uvalue) (b : DV2.uvalue) => uvalue_convert_strict a = NoOom b /\ DV2.uvalue_strict_subterm b (DV2.UVALUE_Struct fields)) x fields).
        { induction H1; cbn; auto.
          constructor.
          - split; eauto.
            repeat constructor.            
          - forward IHForall2.
            { intros u H2 u1 H3.
              apply H; eauto.
              eapply uvalue_strict_subterm_struct; eauto.
            }

            eapply Forall2_impl; eauto.
            intros a b H2.
            cbn in H2.
            destruct H2.
            split; eauto.
            eapply uvalue_strict_subterm_struct; eauto.
        }

        eapply orutt_bind with (RR:=Forall2 dvalue_refine_strict).
        { eapply map_monad_orutt2.
          apply H0.

          intros ? ? ?; cbn in *.
          destruct H2 as (?&?).
          eapply H; eauto.
        }
        intros r1 r2 H2.
        apply orutt_Ret.
        eapply map_monad_oom_Forall2 in H2.
        rewrite dvalue_refine_strict_equation; cbn;
          rewrite H2; cbn.
        reflexivity.
      + (* Packed Structs *)
        cbn.
        eapply map_monad_oom_Forall2 in H1.
        assert (Forall2 (fun (a : DV1.uvalue) (b : DV2.uvalue) => uvalue_convert_strict a = NoOom b /\ DV2.uvalue_strict_subterm b (DV2.UVALUE_Packed_struct fields)) x fields).
        { induction H1; cbn; auto.
          constructor.
          - split; eauto.
            repeat constructor.            
          - forward IHForall2.
            { intros u H2 u1 H3.
              apply H; eauto.
              eapply uvalue_strict_subterm_packed_struct; eauto.
            }

            eapply Forall2_impl; eauto.
            intros a b H2.
            cbn in H2.
            destruct H2.
            split; eauto.
            eapply uvalue_strict_subterm_packed_struct; eauto.
        }

        eapply orutt_bind with (RR:=Forall2 dvalue_refine_strict).
        { eapply map_monad_orutt2.
          apply H0.

          intros ? ? ?; cbn in *.
          destruct H2 as (?&?).
          eapply H; eauto.
        }
        intros r1 r2 H2.
        apply orutt_Ret.
        eapply map_monad_oom_Forall2 in H2.
        rewrite dvalue_refine_strict_equation; cbn;
          rewrite H2; cbn.
        reflexivity.
      + (* Arrays *)
        cbn.
        eapply map_monad_oom_Forall2 in H1.
        assert (Forall2 (fun (a : DV1.uvalue) (b : DV2.uvalue) => uvalue_convert_strict a = NoOom b /\ DV2.uvalue_strict_subterm b (DV2.UVALUE_Array t elts)) x elts).
        { induction H1; cbn; auto.
          constructor.
          - split; eauto.
            repeat constructor.            
          - forward IHForall2.
            { intros u H2 u1 H3.
              apply H; eauto.
              eapply uvalue_strict_subterm_array; eauto.
            }

            eapply Forall2_impl; eauto.
            intros a b H2.
            cbn in H2.
            destruct H2.
            split; eauto.
            eapply uvalue_strict_subterm_array; eauto.
        }

        eapply orutt_bind with (RR:=Forall2 dvalue_refine_strict).
        { eapply map_monad_orutt2.
          apply H0.

          intros ? ? ?; cbn in *.
          destruct H2 as (?&?).
          eapply H; eauto.
        }
        intros r1 r2 H2.
        apply orutt_Ret.
        eapply map_monad_oom_Forall2 in H2.
        rewrite dvalue_refine_strict_equation; cbn;
          rewrite H2; cbn.
        reflexivity.
      + (* Vectors *)
        cbn.
        eapply map_monad_oom_Forall2 in H1.
        assert (Forall2 (fun (a : DV1.uvalue) (b : DV2.uvalue) => uvalue_convert_strict a = NoOom b /\ DV2.uvalue_strict_subterm b (DV2.UVALUE_Vector t elts)) x elts).
        { induction H1; cbn; auto.
          constructor.
          - split; eauto.
            repeat constructor.            
          - forward IHForall2.
            { intros u H2 u1 H3.
              apply H; eauto.
              eapply uvalue_strict_subterm_vector; eauto.
            }

            eapply Forall2_impl; eauto.
            intros a b H2.
            cbn in H2.
            destruct H2.
            split; eauto.
            eapply uvalue_strict_subterm_vector; eauto.
        }

        eapply orutt_bind with (RR:=Forall2 dvalue_refine_strict).
        { eapply map_monad_orutt2.
          apply H0.

          intros ? ? ?; cbn in *.
          destruct H2 as (?&?).
          eapply H; eauto.
        }
        intros r1 r2 H2.
        apply orutt_Ret.
        eapply map_monad_oom_Forall2 in H2.
        rewrite dvalue_refine_strict_equation; cbn;
          rewrite H2; cbn.
        reflexivity.
      + (* IBinop *)
        cbn.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? ?.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? ?.
        apply orutt_eval_iop; auto.
      + (* ICmp *)
        cbn.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? ?.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? ?.
        apply orutt_eval_icmp; auto.
      + (* FBinop *)
        cbn.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? ?.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? ?.
        apply orutt_eval_fop; auto.
      + (* FCmp *)
        cbn.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? ?.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? ?.
        apply orutt_eval_fcmp; auto.
      + (* Conversion *)
        cbn.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? ?.
        erewrite (fin_to_inf_dvalue_refine_strict' r1); eauto.
        remember (get_conv_case conv t_from r2 t_to) as c.
        destruct c; symmetry in Heqc.
        * erewrite get_conv_case_pure_fin_inf; eauto.
          apply orutt_Ret.
          apply fin_to_inf_dvalue_refine_strict.
        * erewrite get_conv_case_itop_fin_inf; eauto.
          remember (ITOP.int_to_ptr (dvalue_int_unsigned x0) PROV.wildcard_prov) as p.
          destruct p; symmetry in Heqp.
          { erewrite int_to_ptr_fin_inf_wildcard with (a_inf:=fin_to_inf_addr a) (a_fin:=a); eauto.
            2: {
              unfold fin_to_inf_addr.
              break_match; clear Heqs; auto.
            }

            apply orutt_Ret.
            red.
            cbn.
            rewrite addr_convert_fin_to_inf_addr; reflexivity.
            rewrite fin_to_inf_dvalue_dvalue_int_unsigned; auto.
          }

          apply orutt_raiseOOM.
        * erewrite get_conv_case_ptoi_fin_inf; eauto.
          destruct x0; cbn;
            rewrite_fin_to_inf_dvalue; cbn;
            try solve
              [ apply orutt_raise;
                [ intros ? ? CONTRA; inv CONTRA | cbn; auto ]
              ].

          destruct t_to;
            try solve
              [ apply orutt_raise;
                [ intros ? ? CONTRA; inv CONTRA | cbn; auto ]
              ].
          { all: apply orutt_Ret;
              rewrite dvalue_refine_strict_equation; cbn;
              rewrite ptr_to_int_fin_to_inf_addr;
              reflexivity.
          }

          rewrite ptr_to_int_fin_to_inf_addr.
          eapply orutt_bind with (RR:=(fun a b => a = intptr_fin_inf b)).
          { unfold lift_OOM.
            break_match.
            - rewrite IS1.LP.IP.VMemInt_intptr_mrepr_from_Z in Heqo.
              rewrite IS2.LP.IP.VMemInt_intptr_mrepr_from_Z.
              apply IS1.LP.IP.from_Z_to_Z in Heqo.
              break_match.
              + apply IP.from_Z_to_Z in Heqo0.
                apply orutt_Ret.
                unfold intptr_fin_inf.
                break_match.
                clear Heqs.
                apply IS1.LP.IP.from_Z_to_Z in e.
                rewrite Heqo0 in e.
                rewrite <- Heqo in e.
                apply IS1.LP.IP.to_Z_inj in e; auto.
              + apply orutt_raiseOOM.
            - break_match.
              + eapply VMEM_REF.mrepr_refine in Heqo0.
                setoid_rewrite Heqo in Heqo0; inv Heqo0.
                rewrite IS1.LP.IP.VMemInt_intptr_mrepr_from_Z in Heqo.
                rewrite IS2.LP.IP.VMemInt_intptr_mrepr_from_Z in Heqo0.
                apply IP.from_Z_to_Z in Heqo0.
                rewrite <- Heqo0 in Heqo.
                pose proof intptr_convert_succeeds i.
                destruct H2.
                rewrite e in Heqo.
                inv Heqo.
              + apply orutt_raiseOOM.
          }

          intros ? ? ?; subst.
          apply orutt_Ret.
          rewrite dvalue_refine_strict_equation.
          cbn.
          unfold intptr_fin_inf.
          break_inner_match.
          clear Heqs.
          apply intptr_convert_safe in e.
          rewrite e.
          reflexivity.
        * (* OOM *)
          apply orutt_raiseOOM.
        * (* Conv_Illegal *)
          erewrite get_conv_case_illegal_fin_inf; eauto.
          apply orutt_raise.
          intros ? ? CONTRA. inv CONTRA.
          cbn; auto.
      + (* GetElementPtr *)
        cbn.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? REF.

        eapply map_monad_oom_Forall2 in H2.
        assert (Forall2 (fun (a : DV1.uvalue) (b : DV2.uvalue) => uvalue_convert_strict a = NoOom b /\ DV2.uvalue_strict_subterm b (DV2.UVALUE_GetElementPtr t u2 idxs)) x0 idxs).
        { induction H2; cbn; auto.
          constructor.
          - split; eauto.
            repeat constructor.
          - forward IHForall2.
            { intros ? ? ? ?.
              apply H; eauto.
              eapply uvalue_strict_subterm_gep_cons; eauto.
            }

            eapply Forall2_impl; eauto.
            intros a b P.
            cbn in P.
            destruct P.
            split; eauto.
            eapply uvalue_strict_subterm_gep_cons; eauto.
        }

        eapply orutt_bind with (RR:=Forall2 dvalue_refine_strict).
        { eapply map_monad_orutt2.
          apply H0.

          intros ? ? ?; cbn in *.
          destruct H3 as (?&?).
          eapply H; eauto.
        }

        intros ? ? ?.
        unfold GEP.handle_gep,
          IS1.LLVM.MEM.MP.GEP.handle_gep.
        destruct r2;
          dvalue_refine_strict_inv REF;
          try solve
            [ apply orutt_raise;
              [ intros ? ? CONTRA; inv CONTRA | cbn; auto ]
            ].

        remember (GEP.handle_gep_addr t a r3) as res.
        destruct res as [res_err | [res | res_oom]];
          symmetry in Heqres.
        * eapply handle_gep_addr_err_fin_inf with (base_addr_inf:=x1) in Heqres; eauto.
          2: {
            apply addr_convert_safe_reverse; auto.
          }

          erewrite <- dvalue_refine_strict_map_fin_to_inf_dvalue in Heqres; eauto.
          rewrite Heqres.
          cbn.
          apply orutt_raise;
            [ intros ? ? CONTRA; inv CONTRA | cbn; auto ].
        * eapply handle_gep_addr_fin_inf
            with (base_addr_inf:=x1) (res_addr_inf:=fin_to_inf_addr res)
            in Heqres; eauto.
          2: apply addr_convert_safe_reverse; auto.
          2: apply addr_convert_safe_reverse; auto; apply addr_refine_fin_to_inf_addr.

          erewrite <- dvalue_refine_strict_map_fin_to_inf_dvalue in Heqres; eauto.
          rewrite Heqres.
          cbn.
          apply orutt_Ret.
          rewrite dvalue_refine_strict_equation.
          cbn.
          rewrite addr_refine_fin_to_inf_addr; reflexivity.
        * cbn.
          apply orutt_raiseOOM.
      + (* ExtractElement *)
        cbn.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? REF.

        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? REF2.

        eapply orutt_bind with (RR:=eq).
        { destruct vec_typ;
            try solve
              [ apply orutt_raise;
                [ intros ? ? CONTRA; inv CONTRA | cbn; auto ]
              ].
          apply orutt_Ret; auto.
        }

        intros ? ? ?; subst.
        apply orutt_index_into_vec_dv; auto.
      + (* InsertElement *)
        cbn.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? REF.

        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? REF2.

        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? REF3.

        apply orutt_insert_into_vec_dv; auto.
      + (* ShuffleVector *)
        cbn.
        (* Currently unimplemented, but will be similar to insert case above *)
        apply orutt_raise;
          [ intros ? ? CONTRA; inv CONTRA | cbn; auto ].
      + (* ExtractValue *)
        cbn.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? REF.
        apply orutt_extractvalue_loop; auto.
      + (* InsertValue *)
        cbn.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? REF.

        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? REF2.
        apply orutt_insert_value_loop; auto.
      + (* Select *)
        cbn.
        eapply orutt_bind;
          [ eapply H; eauto; repeat constructor | ].
        intros ? ? REF.
        destruct r2; dvalue_refine_strict_inv REF;
          try solve
            [ apply orutt_raise;
              [ intros ? ? CONTRA; inv CONTRA | cbn; auto ]
            ].
        { (* ix *)
          repeat break_match_goal;
            try solve
              [ apply orutt_raise;
                [ intros ? ? CONTRA; inv CONTRA | cbn; auto ]
              ];
            eapply H; eauto; repeat constructor.
        }

        { (* poison *)
          apply orutt_Ret.
          solve_dvalue_refine_strict.
        }

        { (* vector *)
          eapply orutt_bind;
            [ eapply H; eauto; repeat constructor | ].
          intros ? ? REF.

          eapply orutt_bind;
            [ eapply H; eauto; repeat constructor | ].
          intros ? ? REF2.

          destruct r2; dvalue_refine_strict_inv REF;
            try solve
              [ apply orutt_raise;
                [ intros ? ? CONTRA; inv CONTRA | cbn; auto ]
              ].

          { (* Poison *)
            apply orutt_Ret;
              solve_dvalue_refine_strict.
          }

          destruct r3;
            dvalue_refine_strict_inv REF2;
            try solve
              [ apply orutt_raise;
                [ intros ? ? CONTRA; inv CONTRA | cbn; auto ]
              ].

          { (* Poison *)
            apply orutt_Ret;
              solve_dvalue_refine_strict.
          }

          eapply orutt_bind with (RR:=Forall2 dvalue_refine_strict).
          {
            apply orutt_eval_select_loop; auto.
          }

          intros ? ? REF.
          apply orutt_Ret.
          rewrite dvalue_refine_strict_equation.
          cbn.
          apply map_monad_oom_Forall2 in REF.
          rewrite REF.
          auto.
        }
      + (* ExtractByte *)
        cbn.
        apply orutt_raise;
          [ intros ? ? CONTRA; inv CONTRA | cbn; auto ].
      + (* ConcatBytes *)
        Opaque concretize_uvalue_bytes_helper.
        Opaque IS2.MEM.CP.CONCBASE.concretize_uvalue_bytes_helper.
        Opaque IS1.MEM.CP.CONCBASE.concretize_uvalue_bytes_helper.
        cbn.
        pose proof (map_monad_oom_length _ _ _ H1) as LEN.
        setoid_rewrite LEN.
        rewrite sizeof_dtyp_fin_inf.
        break_match_goal.
        { (* Size and type match *)
          setoid_rewrite all_extract_bytes_from_uvalue_fin_inf; eauto.
          destruct (all_extract_bytes_from_uvalue dt uvs) eqn:HExtract;
            cbn.
          - apply all_extract_bytes_from_uvalue_success_inv in HExtract.
            destruct HExtract as (?&?&?); subst.
            destruct x; inv H1.
            repeat break_match_hyp_inv.
            uvalue_convert_strict_inv Heqo.
            apply H; auto.
            eapply uvalue_concat_bytes_strict_subterm.
            repeat constructor.
          - eapply orutt_bind with (RR:=dvalue_bytes_refine).
            2: apply orutt_dvalue_bytes_to_dvalue.

            apply orutt_concretize_uvalue_bytes_helper.
            { intros u H0 uv_fin H2.
              apply H; auto.
              eapply uvalue_concat_bytes_strict_subterm; auto.
            }
            apply map_monad_oom_Forall2; auto.
            apply concretization_map_refine_empty.
        }

        { (* Size or type mismatch *)
          eapply orutt_bind with (RR:=dvalue_bytes_refine).
          2: apply orutt_dvalue_bytes_to_dvalue.
          apply orutt_concretize_uvalue_bytes_helper.
          { intros u H0 uv_fin H2.
            apply H; auto.
            eapply uvalue_concat_bytes_strict_subterm; auto.
          }
          apply map_monad_oom_Forall2; auto.
          apply concretization_map_refine_empty.
        }

        Unshelve.
        eapply intptr_fin_inf; eauto.
  Qed.

  Lemma orutt_denote_exp_concretize_if_no_undef_or_poison :
    forall u1 u2,
      uvalue_refine_strict u1 u2 ->
      orutt exp_E_refine_strict exp_E_res_refine_strict uvalue_refine_strict
        (IS1.LLVM.D.concretize_if_no_undef_or_poison u1)
        (concretize_if_no_undef_or_poison u2)
        (OOM:=OOME).
  Proof.
    intros u1 u2 REF.
    unfold IS1.LLVM.D.concretize_if_no_undef_or_poison,
      concretize_if_no_undef_or_poison.
    setoid_rewrite <- contains_undef_or_poison_E1_E2; eauto.
    break_match.
    - apply orutt_Ret; auto.
    - eapply orutt_bind with (RR:=dvalue_refine_strict).
      { apply orutt_concretize_uvalue; auto.
      }

      intros r1 r2 H.
      cbn.
      apply orutt_Ret.
      apply dvalue_refine_strict_dvalue_to_uvalue; auto.
  Qed.

  Lemma orutt_denote_exp'_Zero_initializer:
    forall odt : option dtyp,
      orutt exp_E_refine_strict exp_E_res_refine_strict uvalue_refine_strict
        (IS1.LLVM.D.denote_exp' odt LLVMAst.EXP_Zero_initializer)
        (denote_exp' odt LLVMAst.EXP_Zero_initializer) (OOM := OOME).
  Proof.
    intros odt.
    destruct odt as [dt | ];
      cbn;
      try solve [
          solve_orutt_raise
        ].

    unfold denote_exp, IS1.LLVM.D.denote_exp.
    unfold LLVMEvents.lift_err.

    repeat break_match_goal.
    - cbn in *.
      repeat break_match_hyp_inv.
      unfold IS1.LLVM.D.dv_zero_initializer in Heqs0.
      unfold dv_zero_initializer in *.
      apply default_dvalue_of_dtyp_dv1_dv2_same_error in Heqs0.
      rewrite Heqs0 in Heqs1. inversion Heqs1. subst.
      solve_orutt_raise.
    - cbn in *.
      repeat break_match_hyp_inv.
      unfold IS1.LLVM.D.dv_zero_initializer in Heqs0.
      unfold dv_zero_initializer in *.
      apply default_dvalue_of_dtyp_dv1_dv2_same_error in Heqs0.
      rewrite Heqs0 in Heqs1. inversion Heqs1.
    - cbn in *.
      repeat break_match_hyp_inv.
      unfold IS1.LLVM.D.dv_zero_initializer in Heqs0.
      unfold dv_zero_initializer in *.
      apply DVCrev.default_dvalue_of_dtyp_dv1_dv2_equiv' in Heqs0.
      destruct Heqs0 as [y [Hy _]].
      rewrite Hy in Heqs1. inversion Heqs1.
    - cbn in *.
      repeat break_match_hyp_inv.
      unfold IS1.LLVM.D.dv_zero_initializer in Heqs0.
      unfold dv_zero_initializer in *.

      apply default_dvalue_of_dtyp_dv1_dv2_equiv in Heqs0.
      destruct Heqs0 as [y [Hy HR]].
      rewrite Hy in Heqs1. inversion Heqs1; subst.
      apply orutt_Ret.
      apply dvalue_refine_strict_dvalue_to_uvalue; auto.
  Qed.

  Lemma orutt_denote_exp_Zero_initializer:
    forall odt : option dtyp,
      orutt exp_E_refine_strict exp_E_res_refine_strict uvalue_refine_strict
        (IS1.LLVM.D.denote_exp odt LLVMAst.EXP_Zero_initializer)
        (denote_exp odt LLVMAst.EXP_Zero_initializer) (OOM := OOME).
  Proof.
    intros odt.
    eapply orutt_bind.
    apply orutt_denote_exp'_Zero_initializer.
    apply orutt_denote_exp_concretize_if_no_undef_or_poison.
  Qed.

  Lemma denote_exp'_E1E2_orutt :
    forall e odt,
      orutt exp_E_refine_strict
        exp_E_res_refine_strict uvalue_refine_strict
        (IS1.LLVM.D.denote_exp' odt e)
        (IS2.LLVM.D.denote_exp' odt e)
        (OOM:=OOME).
  Proof.
    intros e.
    induction e using AstLib.exp_ind; intros odt; cbn;
      try solve
        [ match goal with
                   [ b : bool |- _ ] => destruct b; cbn; apply orutt_Ret; solve_uvalue_refine_strict
                 | _ => try solve [
                           simplify_expr odt; apply orutt_Ret; solve_uvalue_refine_strict
                         | cbn;
                           eapply orutt_bind; eauto;
                           intros r1 r2 H;
                           eapply orutt_bind; eauto;
                           intros r0 r3 H0;
                           apply orutt_Ret;

                           rewrite uvalue_refine_strict_equation; cbn;
                           rewrite uvalue_refine_strict_equation in H, H0;
                           rewrite H, H0;
                           reflexivity]
          end
        ].

    - apply translate_LU_to_exp_lookup_id_orutt.

    - simplify_expr odt.
      + repeat rewrite map_ret;
          apply orutt_Ret;
          rewrite uvalue_refine_strict_equation;
          reflexivity.
      + repeat rewrite map_bind.
        eapply orutt_bind with
          (RR:=(fun (ip1 : IS1.LP.IP.intptr) (ip2 : IS2.LP.IP.intptr) => IS1.LP.IP.to_Z ip1 = IS2.LP.IP.to_Z ip2)).
        unfold lift_OOM.
        { break_match; break_match.
          - apply orutt_Ret.
            rewrite IS1.LP.IP.VMemInt_intptr_mrepr_from_Z in Heqo.
            rewrite IS2.LP.IP.VMemInt_intptr_mrepr_from_Z in Heqo0.
            erewrite IP.from_Z_to_Z; eauto.
            erewrite IS1.LP.IP.from_Z_to_Z; eauto.
          - apply orutt_raise_oom.
          - (* TODO: Maybe this should be a lemma *)
            rewrite IS1.LP.IP.VMemInt_intptr_mrepr_from_Z in Heqo.
            rewrite IS2.LP.IP.VMemInt_intptr_mrepr_from_Z in Heqo0.

            pose proof intptr_convert_succeeds i as [i2 CONV].
            rewrite IP.from_Z_to_Z with (i:=i) (z:=x) in CONV; eauto.
            rewrite Heqo in CONV. inv CONV.
          - apply orutt_raise_oom.
        }

        intros r1 r2 H.
        do 2 rewrite map_ret.
        apply orutt_Ret.
        cbn.
        rewrite uvalue_refine_strict_equation.
        cbn.
        rewrite H.
        rewrite IP.to_Z_from_Z; auto.

    - apply orutt_denote_exp'_Zero_initializer.

    - (* CStrings *)
      eapply orutt_bind with
        (RR:=(fun uvs1 uvs2 =>
                Forall2 uvalue_refine_strict uvs1 uvs2)
        ).
      + unfold uvalue_refine_strict. cbn.
        revert H.
        induction elts; intros; cbn in *.
        * apply orutt_Ret.
          cbn.  constructor.
        * destruct a.
          eapply orutt_bind with (RR:=(fun uvs1 uvs2 => uvalue_refine_strict uvs1 uvs2)).
          -- eapply (H (d,e)). left; auto.
          -- intros.
             eapply orutt_bind with (RR:=(fun uvs1 uvs2 => Forall2 uvalue_refine_strict uvs1 uvs2)).
             ++ apply IHelts.
                intros.
                apply H.
                right. assumption.
             ++ intros.
                apply orutt_Ret.
                constructor; auto.
      + intros.
        apply orutt_Ret.
        unfold uvalue_refine_strict.
        cbn.
        unfold uvalue_refine_strict in H0.
        break_match_goal.
        * rewrite map_monad_oom_Forall2 in Heqo.
          rewrite (Forall2_ext_m _ _ _ _ H0 Heqo).
          reflexivity.
        * apply map_monad_OOM_fail in Heqo.
          destruct Heqo as [v [HI HC]].
          destruct (Forall2_In _ _ _ _ HI H0) as [x [HJ HX]].
          rewrite HC in HX.
          inversion HX.

    - (* Structs *)
      eapply orutt_bind with
        (RR:=(fun uvs1 uvs2 =>
                Forall2 uvalue_refine_strict uvs1 uvs2)
        ).
      + unfold uvalue_refine_strict. cbn.
        revert H.
        induction fields; intros; cbn in *.
        * apply orutt_Ret.
          cbn.  constructor.
        * destruct a.
          eapply orutt_bind with (RR:=(fun uvs1 uvs2 => uvalue_refine_strict uvs1 uvs2)).
          -- eapply (H (d,e)). left; auto.
          -- intros.
             eapply orutt_bind with (RR:=(fun uvs1 uvs2 => Forall2 uvalue_refine_strict uvs1 uvs2)).
             ++ apply IHfields.
                intros.
                apply H.
                right. assumption.
             ++ intros.
                apply orutt_Ret.
                constructor; auto.
      + intros.
        apply orutt_Ret.
        unfold uvalue_refine_strict.
        cbn.
        unfold uvalue_refine_strict in H0.
        break_match_goal.
        * rewrite map_monad_oom_Forall2 in Heqo.
          rewrite (Forall2_ext_m _ _ _ _ H0 Heqo).
          reflexivity.
        * apply map_monad_OOM_fail in Heqo.
          destruct Heqo as [v [HI HC]].
          destruct (Forall2_In _ _ _ _ HI H0) as [x [HJ HX]].
          rewrite HC in HX.
          inversion HX.

    - (* Packed_structs *)
      simplify_expr odt.
      eapply orutt_bind with
        (RR:=(fun uvs1 uvs2 =>
                Forall2 uvalue_refine_strict uvs1 uvs2)
        ).
      + unfold uvalue_refine_strict. cbn.
        revert H.
        induction fields; intros; cbn in *.
        * apply orutt_Ret.
          cbn.  constructor.
        * destruct a.
          eapply orutt_bind with (RR:=(fun uvs1 uvs2 => uvalue_refine_strict uvs1 uvs2)).
          -- eapply (H (d,e)). left; auto.
          -- intros.
             eapply orutt_bind with (RR:=(fun uvs1 uvs2 => Forall2 uvalue_refine_strict uvs1 uvs2)).
             ++ apply IHfields.
                intros.
                apply H.
                right. assumption.
             ++ intros.
                apply orutt_Ret.
                constructor; auto.
      + intros.
        apply orutt_Ret.
        unfold uvalue_refine_strict.
        cbn.
        unfold uvalue_refine_strict in H0.
        break_match_goal.
        * rewrite map_monad_oom_Forall2 in Heqo.
          rewrite (Forall2_ext_m _ _ _ _ H0 Heqo).
          reflexivity.
        * apply map_monad_OOM_fail in Heqo.
          destruct Heqo as [v [HI HC]].
          destruct (Forall2_In _ _ _ _ HI H0) as [x [HJ HX]].
          rewrite HC in HX.
          inversion HX.

    - (* Arrays *)
      eapply orutt_bind with
        (RR:=(fun uvs1 uvs2 =>
                Forall2 uvalue_refine_strict uvs1 uvs2)
        ).
      + unfold uvalue_refine_strict. cbn.
        revert H.
        induction elts; intros; cbn in *.
        * apply orutt_Ret.
          cbn.  constructor.
        * destruct a.
          eapply orutt_bind with (RR:=(fun uvs1 uvs2 => uvalue_refine_strict uvs1 uvs2)).
          -- eapply (H (d,e)). left; auto.
          -- intros.
             eapply orutt_bind with (RR:=(fun uvs1 uvs2 => Forall2 uvalue_refine_strict uvs1 uvs2)).
             ++ apply IHelts.
                intros.
                apply H.
                right. assumption.
             ++ intros.
                apply orutt_Ret.
                constructor; auto.
      + intros.
        apply orutt_Ret.
        unfold uvalue_refine_strict.
        cbn.
        unfold uvalue_refine_strict in H0.
        break_match_goal.
        * rewrite map_monad_oom_Forall2 in Heqo.
          rewrite (Forall2_ext_m _ _ _ _ H0 Heqo).
          reflexivity.
        * apply map_monad_OOM_fail in Heqo.
          destruct Heqo as [v [HI HC]].
          destruct (Forall2_In _ _ _ _ HI H0) as [x [HJ HX]].
          rewrite HC in HX.
          inversion HX.

    - (* Vectors *)
      eapply orutt_bind with
        (RR:=(fun uvs1 uvs2 =>
                Forall2 uvalue_refine_strict uvs1 uvs2)
        ).
      + unfold uvalue_refine_strict. cbn.
        revert H.
        induction elts; intros; cbn in *.
        * apply orutt_Ret.
          cbn.  constructor.
        * destruct a.
          eapply orutt_bind with (RR:=(fun uvs1 uvs2 => uvalue_refine_strict uvs1 uvs2)).
          -- eapply (H (d,e)). left; auto.
          -- intros.
             eapply orutt_bind with (RR:=(fun uvs1 uvs2 => Forall2 uvalue_refine_strict uvs1 uvs2)).
             ++ apply IHelts.
                intros.
                apply H.
                right. assumption.
             ++ intros.
                apply orutt_Ret.
                constructor; auto.
      + intros.
        apply orutt_Ret.
        unfold uvalue_refine_strict.
        cbn.
        unfold uvalue_refine_strict in H0.
        break_match_goal.
        * rewrite map_monad_oom_Forall2 in Heqo.
          rewrite (Forall2_ext_m _ _ _ _ H0 Heqo).
          reflexivity.
        * apply map_monad_OOM_fail in Heqo.
          destruct Heqo as [v [HI HC]].
          destruct (Forall2_In _ _ _ _ HI H0) as [x [HJ HX]].
          rewrite HC in HX.
          inversion HX.

    - (* Conversion *)
      cbn.
      eapply orutt_bind; eauto.
      intros r1 r2 H.
      apply orutt_Ret.
      rewrite uvalue_refine_strict_equation; cbn;
        rewrite uvalue_refine_strict_equation in H.
      rewrite H.
      cbn.
      reflexivity.

    - (* GetElementPtr *)
      destruct ptrval as [ptr_t ptrval].
      cbn.
      eapply orutt_bind; eauto.
      intros r1 r2 H0.

      eapply orutt_bind with
        (RR:=(fun uvs1 uvs2 =>
                Forall2 uvalue_refine_strict uvs1 uvs2)
        ).
      + unfold uvalue_refine_strict. cbn.
        revert H.
        induction idxs; intros; cbn in *.
        * apply orutt_Ret.
          cbn.  constructor.
        * destruct a.
          eapply orutt_bind with (RR:=(fun uvs1 uvs2 => uvalue_refine_strict uvs1 uvs2)).
          -- eapply (H (d,e)). left; auto.
          -- intros.
             eapply orutt_bind with (RR:=(fun uvs1 uvs2 => Forall2 uvalue_refine_strict uvs1 uvs2)).
             ++ apply IHidxs.
                intros.
                apply H.
                right. assumption.
             ++ intros.
                apply orutt_Ret.
                constructor; auto.
      + intros.
        apply orutt_Ret.
        unfold uvalue_refine_strict.
        cbn.
        unfold uvalue_refine_strict in H0.
        rewrite H0.
        break_match_goal.
        * rewrite map_monad_oom_Forall2 in Heqo.
          rewrite (Forall2_ext_m _ _ _ _ H1 Heqo).
          reflexivity.
        * apply map_monad_OOM_fail in Heqo.
          destruct Heqo as [v [HI HC]].
          destruct (Forall2_In _ _ _ _ HI H1) as [x [HJ HX]].
          unfold uvalue_refine_strict in HX.
          rewrite HC in HX.
          inversion HX.

    - (* ExtractElement *)
      destruct vec as [vec_t vec].
      destruct idx as [idx_t idx].
      cbn.

      eapply orutt_bind; eauto.
      intros r1 r2 H.
      eapply orutt_bind; eauto.
      intros r0 r3 H0.
      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation; cbn.
      rewrite uvalue_refine_strict_equation in H0, H.
      cbn.
      rewrite H, H0.
      reflexivity.

    - (* InsertElement *)
      destruct vec as [vec_t vec].
      destruct idx as [idx_t idx].
      destruct elt as [elt_t elt].
      cbn.

      eapply orutt_bind; eauto.
      intros r1 r2 H.

      eapply orutt_bind; eauto.
      intros r0 r3 H0.

      eapply orutt_bind; eauto.
      intros r4 r5 H1.

      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation; cbn.
      rewrite uvalue_refine_strict_equation in H, H0, H1.
      cbn.

      rewrite H, H0, H1.
      reflexivity.

    - (* ShuffleVector *)
      destruct vec1 as [vec1_t vec1].
      destruct vec2 as [vec2_t vec2].
      destruct idxmask as [idxmask_t idxmask].
      cbn.

      eapply orutt_bind; eauto.
      intros r1 r2 H.

      eapply orutt_bind; eauto.
      intros r0 r3 H0.

      eapply orutt_bind; eauto.
      intros r4 r5 H1.

      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation; cbn.
      rewrite uvalue_refine_strict_equation in H, H0, H1.
      cbn.

      rewrite H, H0, H1.
      reflexivity.

    - (* ExtractValue *)
      destruct vec as [vec_t vec].
      cbn.

      eapply orutt_bind; eauto.
      intros r1 r2 H.

      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation; cbn.
      rewrite uvalue_refine_strict_equation in H.
      cbn.

      rewrite H.
      reflexivity.

    - (* InsertValue *)
      destruct vec as [vec_t vec].
      destruct elt as [elt_t elt].
      cbn.

      eapply orutt_bind; eauto.
      intros r1 r2 H.

      eapply orutt_bind; eauto.
      intros r0 r3 H0.

      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation; cbn.
      rewrite uvalue_refine_strict_equation in H, H0.
      cbn.

      rewrite H, H0.
      reflexivity.

    - (* Select *)
      destruct cnd, v1, v2.
      cbn.

      eapply orutt_bind; eauto.
      intros r1 r2 H.

      eapply orutt_bind; eauto.
      intros r0 r3 H0.

      eapply orutt_bind; eauto.
      intros r4 r5 H1.

      apply orutt_Ret.

      rewrite uvalue_refine_strict_equation; cbn.
      rewrite uvalue_refine_strict_equation in H, H0, H1.
      cbn.

      rewrite H, H0, H1.
      reflexivity.

    - (* Freeze *)
      destruct v; cbn.
      eapply orutt_bind; eauto.
      intros r1 r2 H.

      eapply orutt_bind with (RR:=dvalue_refine_strict); eauto.
      apply pick_your_poison_orutt; auto.
      intros r0 r3 H0.
      apply orutt_Ret.
      apply dvalue_refine_strict_dvalue_to_uvalue; auto.
  Qed.

  Lemma denote_exp_E1E2_orutt :
    forall e odt,
      orutt exp_E_refine_strict
        exp_E_res_refine_strict uvalue_refine_strict
        (IS1.LLVM.D.denote_exp odt e)
        (IS2.LLVM.D.denote_exp odt e)
        (OOM:=OOME).
  Proof.
    intros e odt.
    eapply orutt_bind; eauto.
    apply denote_exp'_E1E2_orutt.
    apply orutt_denote_exp_concretize_if_no_undef_or_poison.
  Qed.

  Lemma initialize_global_E1E2_orutt :
    forall g,
      orutt exp_E_refine_strict exp_E_res_refine_strict eq
        (LLVM1.initialize_global g)
        (LLVM2.initialize_global g)
        (OOM:=OOME).
  Proof.
    intros g.
    cbn.
    eapply orutt_bind with (RR:=dvalue_refine_strict).
    { apply rutt_orutt.
      apply GlobalRead_exp_E_E1E2_rutt.
      intros A e2.
      apply exp_E_dec_oom.
    }

    intros r1 r2 R1R2.
    apply orutt_bind with (RR:=uvalue_refine_strict).
    { break_match.
      apply denote_exp_E1E2_orutt.
      eapply orutt_Ret.
      solve_uvalue_refine_strict.
    }

    intros r3 r4 R3R4.
    apply rutt_orutt; [| apply exp_E_dec_oom].
    apply Store_E1E2_rutt; auto.
  Qed.

  Lemma initialize_globals_E1E2_orutt :
    forall m_globals,
      orutt exp_E_refine_strict exp_E_res_refine_strict eq
        (map_monad LLVM1.initialize_global m_globals)
        (map_monad initialize_global m_globals)
        (OOM:=OOME).
  Proof.
    cbn.

    induction m_globals.
    { cbn.
      apply orutt_Ret.
      reflexivity.
    }
    { rewrite map_monad_unfold.
      rewrite map_monad_unfold.

      apply orutt_bind with (RR:=eq).
      apply initialize_global_E1E2_orutt.

      intros [] [] _.
      apply orutt_bind with (RR:=eq).
      apply IHm_globals.

      intros r1 r2 R1R2; subst.
      apply orutt_Ret.
      reflexivity.
    }
  Qed.

  Lemma build_global_environment_E1E2_orutt_strict_sound :
    forall (m : mcfg dtyp),
      orutt
        event_refine_strict
        event_res_refine_strict
        eq
        (LLVM1.build_global_environment m)
        (LLVM2.build_global_environment m)
        (OOM:=OOME).
  Proof.
    destruct m.
    cbn.
    apply orutt_bind with (RR:=eq).
    { apply orutt_bind with (RR:=eq).
      (* In the future this allocate_one_E1E2_rutt_strict_sound lemma may be orutt *)
      apply rutt_orutt; [| apply L0_dec_oom].
      apply allocate_one_E1E2_rutt_strict_sound.
      intros r1 r2 EQ; subst.
      apply orutt_Ret; auto.
    }

    intros r1 r2 EQ; subst.
    inv r2.

    apply orutt_bind with (RR:=eq).
    { apply orutt_bind with (RR:=eq).
      apply rutt_orutt; [| apply L0_dec_oom].
      apply allocate_global_E1E2_rutt_strict_sound.
      intros r1 r2 EQ; subst.
      apply orutt_Ret; auto.
    }

    intros r1 r2 EQ; subst.
    inv r2.

    eapply translate_exp_to_L0_E1E2_orutt.
    apply orutt_bind with (RR:=eq).
    apply initialize_globals_E1E2_orutt.

    intros r1 r2 R1R2; subst.
    apply orutt_Ret.
    reflexivity.
  Qed.

  Lemma denote_phi_orutt :
    forall bid_from id_p,
      orutt exp_E_refine_strict exp_E_res_refine_strict (eq × uvalue_refine_strict)
        (IS1.LLVM.D.denote_phi bid_from id_p) (denote_phi bid_from id_p)
        (OOM:=OOME).
  Proof.
    intros bid_from id_p.
    destruct id_p as [lid phi].
    destruct phi.
    cbn.
    break_match_goal.
    - cbn.
      eapply orutt_bind with (RR:=uvalue_refine_strict).
      + apply denote_exp_E1E2_orutt.
      + intros r1 r2 REF.
        apply orutt_Ret.
        constructor; cbn; auto.
    - apply orutt_raise; cbn; auto.
      intros msg o CONTRA.
      inv CONTRA.
  Qed.

  Lemma denote_phis_orutt_strict_helper :
    forall phis bid_from,
      orutt instr_E_refine_strict instr_E_res_refine_strict (Forall2 (eq × uvalue_refine_strict))
        (map_monad
           (fun x => translate IS1.LP.Events.exp_to_instr (IS1.LLVM.D.denote_phi bid_from x))
           phis)
        (map_monad
           (fun x => translate exp_to_instr (denote_phi bid_from x))
           phis)
        (OOM:=OOME).
  Proof.
    induction phis; intros bid_from.
    - cbn.
      apply orutt_Ret.
      constructor.
    - repeat rewrite map_monad_unfold.
      eapply orutt_bind with (RR:=eq × uvalue_refine_strict).
      { apply translate_exp_to_instr_E1E2_orutt_strict.
        apply denote_phi_orutt.
      }

      intros [id1 uv1] [id2 uv2] [EQid EQuv].
      cbn in EQid, EQuv; subst.

      cbn.
      eapply orutt_bind with (RR:=Forall2 (eq × uvalue_refine_strict)); eauto.

      intros r1 r2 H.
      apply orutt_Ret.
      apply Forall2_cons.
      + constructor; cbn; auto.
      + auto.
  Qed.

  Lemma denote_phis_orutt_strict :
    forall phis bid_from,
      orutt instr_E_refine_strict instr_E_res_refine_strict eq
        (IS1.LLVM.D.denote_phis bid_from phis) (denote_phis bid_from phis)
        (OOM:=OOME).
  Proof.
    intros phis bid_from.
    cbn.
    eapply orutt_bind with (RR:=Forall2 (eq × uvalue_refine_strict)).
    { apply denote_phis_orutt_strict_helper.
    }

    intros r1 r2 H.
    eapply orutt_bind with (RR:=eq).
    { induction H.
      - cbn.
        apply orutt_Ret.
        reflexivity.
      - repeat rewrite map_monad_unfold.
        destruct x, y.
        cbn.
        eapply orutt_bind with (RR:=eq).
        { eapply orutt_trigger; cbn.
          inv H; auto.

          intros [] [] H1; auto.

          intros o CONTRA.
          inv CONTRA.
        }

        intros [] [] ?; subst.
        eapply orutt_bind with (RR:=eq); eauto.

        intros r1 r2 EQ; subst.
        eapply orutt_Ret; auto.
    }

    intros r0 r3 H0; subst.
    eapply orutt_Ret; auto.
  Qed.

  Transparent uvalue_refine_strict.
  Lemma denote_op_orutt_strict :
    forall op,
      orutt exp_E_refine_strict exp_E_res_refine_strict uvalue_refine_strict
        (IS1.LLVM.D.denote_op op)
        (denote_op op)
        (OOM:=OOME).
  Proof.
    intros op.
    eapply orutt_bind; [| apply orutt_denote_exp_concretize_if_no_undef_or_poison].
    apply denote_exp'_E1E2_orutt.
  Qed.

  Lemma denote_instr_orutt_strict :
    forall instr varg1 varg2,
      OptionUtil.option_rel2 addr_refine varg1 varg2 ->
      orutt instr_E_refine_strict instr_E_res_refine_strict eq
        (IS1.LLVM.D.denote_instr instr varg1)
        (denote_instr instr varg2)
        (OOM:=OOME).
  Proof.
    Opaque denote_exp.
    intros [[id | id] instr] varg1 varg2 VARG.
    { cbn.
      destruct instr; try solve_orutt_raise.
      - apply orutt_raise; cbn; auto.
        intros msg0 o CONTRA.
        inv CONTRA.
      - apply orutt_bind with (RR:=uvalue_refine_strict).
        { apply translate_exp_to_instr_E1E2_orutt_strict.
          apply denote_op_orutt_strict.
        }

        intros r1 r2 H.
        eapply orutt_trigger; cbn.
        inv H; auto.

        intros [] [] H1; auto.

        intros o CONTRA.
        inv CONTRA.

      - destruct fn.
        apply orutt_bind with (RR:=Forall2 uvalue_refine_strict).
        { apply map_monad_orutt.
          intros [? ?].
          apply translate_exp_to_instr_E1E2_orutt_strict.
          apply denote_exp_E1E2_orutt.
        }

        intros r1 r2 H.
        break_match_goal.
        { break_match_goal; [|break_match_goal; [|break_match_goal]].
          - (* va_start *)
            eapply orutt_bind with (RR:=uvalue_refine_strict).
            + destruct args; try solve_orutt_raise.
              destruct p, t.
              destruct args; try solve_orutt_raise.
              destruct varg1, varg2; inv VARG; try solve_orutt_raise.

              eapply orutt_bind with (RR:=uvalue_refine_strict).
              * apply translate_exp_to_instr_E1E2_orutt_strict.
                apply denote_exp_E1E2_orutt.
              * intros r0 r3 H0.
                eapply orutt_bind with (RR:=dvalue_refine_strict).
                eapply pickUnique_instr_E_orutt_strict; eauto.
                intros ? ? ?.
                destruct r5; dvalue_refine_strict_inv H2; try solve_orutt_raiseUB.
                all: try (apply orutt_bind with (RR:=Logic.eq);
                     [ apply orutt_trigger; cbn; eauto;
                       [ repeat split;
                         solve [ red; cbn;
                                 rewrite H2; auto
                               | red; cbn;
                                 rewrite H1; auto
                               | red; cbn;
                                 rewrite H3; auto
                               | eauto
                           ]
                       | intros [] [] ?; auto
                       | intros o CONTRA; inv CONTRA
                       ]
                     | intros ? ? ?;
                         apply orutt_Ret;
                       solve_uvalue_refine_strict
                       ]).
            + intros ? ? ?.
              apply orutt_trigger; cbn; auto.
              intros [] [] ?; auto.
              intros o CONTRA; unfold subevent in CONTRA; inv CONTRA.
          - (* va_copy *)
            eapply orutt_bind with (RR:=uvalue_refine_strict).
            + destruct args; try solve_orutt_raise.
              destruct p, t.
              destruct args; try solve_orutt_raise.
              destruct d0; try solve_orutt_raise.
              destruct d0; try solve_orutt_raise.
              destruct p, t.
              destruct d0; try solve_orutt_raise.
              destruct args; try solve_orutt_raise.
              eapply orutt_bind with (RR:=uvalue_refine_strict).
              * apply translate_exp_to_instr_E1E2_orutt_strict.
                apply denote_exp_E1E2_orutt.
              * intros r0 r3 H0.
                eapply orutt_bind with (RR:=dvalue_refine_strict).
                eapply pickUnique_instr_E_orutt_strict; eauto.
                intros ? ? ?.
                eapply orutt_bind with (RR:=uvalue_refine_strict).
                { apply translate_exp_to_instr_E1E2_orutt_strict.
                  apply denote_exp_E1E2_orutt.
                }

                intros ? ? ?.
                eapply orutt_bind with (RR:=dvalue_refine_strict).
                eapply pickUnique_instr_E_orutt_strict; eauto.
                intros ? ? ?.
                eapply orutt_bind with (RR:=uvalue_refine_strict).
                { apply orutt_trigger; cbn; eauto.
                  intros t1 t2 H4.
                  apply H4.
                  intros ? CONTRA; inv CONTRA.
                }

                intros ? ? ?.
                eapply orutt_bind with (RR:=Logic.eq).
                { apply orutt_trigger; cbn; eauto.
                  intros [] [] ?; auto.
                  intros ? CONTRA; inv CONTRA.
                }

                intros [] [] _.
                apply orutt_Ret.
                solve_uvalue_refine_strict.
            + intros ? ? ?.
              apply orutt_trigger; cbn; auto.
              intros [] [] ?; auto.
              intros o CONTRA; unfold subevent in CONTRA; inv CONTRA.
          - (* va_end *)
            eapply orutt_bind with (RR:=uvalue_refine_strict).
            apply orutt_Ret; try solve_uvalue_refine_strict.
            intros ? ? ?.
            apply orutt_trigger.
            repeat constructor; auto.
            intros [] [] _; auto.
            intros ? CONTRA; inv CONTRA.
          - eapply orutt_bind with (RR:=uvalue_refine_strict).
            + eapply orutt_bind with (RR:=Forall2 dvalue_refine_strict).
              * eapply map_monad_orutt2; eauto.
                intros * ?.
                eapply pickUnique_instr_E_orutt_strict; eauto.
              * intros r0 r3 H0.
                eapply orutt_map.
                -- apply orutt_trigger; cbn; eauto.
                   ++ intros * ?.
                      apply H1.
                   ++ intros ? CONTRA.
                      inv CONTRA.
                -- intros r4 r5 H1.
                   cbn in *.
                   apply dvalue_refine_strict_dvalue_to_uvalue; eauto.
                   apply H1.
            + intros r0 r3 H0.
              eapply orutt_trigger; cbn; eauto.
              * intros [] [] ?; auto.
              * intros o CONTRA.
                inv CONTRA.
        }

        apply orutt_bind with (RR:=uvalue_refine_strict).
        { - eapply orutt_bind with (RR:=uvalue_refine_strict).
            { apply translate_exp_to_instr_E1E2_orutt_strict.
              apply denote_exp_E1E2_orutt.
            }
            intros r0 r3 H0.

            eapply orutt_trigger; cbn; try tauto.
            intros o CONTRA.
            unfold subevent in CONTRA.
            inv CONTRA.
        }

        intros r0 r3 H0.
        eapply orutt_trigger; cbn; try tauto.
        intros [] [] _; auto.
        intros o CONTRA.
        inv CONTRA.
      - break_inner_match.
        { break_inner_match;
            try
              solve
              [ cbn;
                eapply orutt_bind with (RR:=dvalue_refine_strict);
                [ eapply orutt_trigger; cbn; try tauto;
                  intros o CONTRA;
                  inv CONTRA
                |
                ];

                intros r1 r2 H;
                eapply orutt_trigger; cbn; try tauto;
                [ split; auto; eapply dvalue_refine_strict_dvalue_to_uvalue; eauto
                | intros [] [] _; auto
                | intros o CONTRA; inv CONTRA
                ]
              ].

          destruct t0.
          eapply orutt_bind with (RR:=uvalue_refine_strict).
          { apply translate_exp_to_instr_E1E2_orutt_strict.
            apply denote_exp_E1E2_orutt.
          }

          intros r1 r2 H.
          eapply orutt_bind with (RR:=dvalue_refine_strict).
          apply pickUnique_instr_E_orutt_strict; auto.

          intros r0 r3 H0.
          eapply orutt_bind with (RR:=dvalue_refine_strict).
          { eapply orutt_trigger; cbn; try tauto.
            2: intros o CONTRA; inv CONTRA.

            split; auto.
            split; auto.

            erewrite dvalue_int_unsigned_E1E2; eauto.
          }

          intros r4 r5 H1.
          eapply orutt_trigger; cbn; try tauto;
            [ split; auto; eapply dvalue_refine_strict_dvalue_to_uvalue; eauto
            | intros [] [] _; auto
            | intros o CONTRA; inv CONTRA
            ].
        }

        { apply orutt_bind with (RR:=dvalue_refine_strict).
          eapply orutt_trigger; cbn; try tauto; intros o CONTRA; inv CONTRA.

          intros r1 r2 H.
          eapply orutt_trigger; cbn; try tauto;
            [ split; auto; eapply dvalue_refine_strict_dvalue_to_uvalue; eauto
            | intros [] [] _; auto
            | intros o CONTRA; inv CONTRA
            ].
        }

      - destruct ptr.
        eapply orutt_bind.
        { apply translate_exp_to_instr_E1E2_orutt_strict.
          apply denote_exp_E1E2_orutt.
        }

        intros r1 r2 H.
        eapply orutt_bind.
        { apply pickUnique_instr_E_orutt_strict; auto.
        }

        intros r0 r3 H0.
        eapply orutt_bind.
        { apply orutt_trigger; cbn; auto.
          intros t1 t2 H1.
          apply H1.

          intros o CONTRA; inv CONTRA.
        }

        intros r4 r5 H1.
        cbn in H1.
        apply orutt_trigger; cbn; auto.
        tauto.
        intros [] [] _; auto.
        intros o CONTRA; inv CONTRA.
      - apply orutt_raise; cbn; auto.
        intros msg o0 CONTRA; inv CONTRA.
      - (* va_arg *)
        break_match_goal; subst.
        eapply orutt_bind with (RR:=uvalue_refine_strict).
        { apply translate_exp_to_instr_E1E2_orutt_strict.
          apply denote_exp_E1E2_orutt.
        }

        intros ? ? ?.
        eapply orutt_bind.
        { apply pickUnique_instr_E_orutt_strict; auto.
        }

        intros ? ? ?.
        eapply orutt_bind with (RR:=uvalue_refine_strict).
        { apply orutt_trigger; cbn; eauto.
          intros ? ? REF; apply REF.
          intros ? CONTRA; inv CONTRA.
        }

        intros ? ? ?.
        eapply orutt_bind.
        { apply pickUnique_instr_E_orutt_strict; auto.
        }

        intros ? ? ?.
        eapply orutt_bind with (RR:=uvalue_refine_strict).
        { apply orutt_trigger; cbn; eauto.
          intros ? ? REF; apply REF.
          intros ? CONTRA; inv CONTRA.
        }

        intros ? ? ?.
        eapply orutt_bind with (RR:= fun a b => intptr_fin_inf b = a).
        { unfold lift_OOM.
          destruct (IP.from_Z 1) eqn:FROM.
          - pose proof intptr_convert_succeeds i as (?&?).
            erewrite IP.from_Z_to_Z in e0; eauto.
            rewrite e0.
            apply orutt_Ret.
            unfold intptr_fin_inf.
            break_match.
            clear Heqs.
            erewrite IP.from_Z_to_Z in e1; eauto.
            rewrite e0 in e1; inv e1; auto.
          - apply orutt_raise_oom.
        }

        intros ? ? IP_FIN_INF.
        eapply orutt_bind with (RR:=dvalue_refine_strict).
        { unfold lift_err_oom_RAISE_ERROR_OOM.
          destruct (GEP.handle_gep t r7 [DVALUE_IPTR r11]) eqn:GEP.

          (* TODO: Move this *)
          Set Nested Proofs Allowed.
          Lemma handle_gep_err_fin_inf :
            forall t base_addr_fin base_addr_inf idxs_fin idxs_inf msg,
              GEP.handle_gep t base_addr_fin idxs_fin = inl msg ->
              map fin_to_inf_dvalue idxs_fin = idxs_inf ->
              dvalue_refine_strict base_addr_inf base_addr_fin ->
              IS1.LLVM.MEM.MP.GEP.handle_gep t base_addr_inf idxs_inf = inl msg.
          Proof.
            intros t base_addr_fin base_addr_inf
              idxs_fin idxs_inf
              msg GEP IDXS BASE_ADDR.

            unfold IS1.LLVM.MEM.MP.GEP.handle_gep, GEP.handle_gep in *.
            break_match_hyp_inv; dvalue_refine_strict_inv BASE_ADDR; auto.
            break_match_hyp_inv.
            eapply handle_gep_addr_err_fin_inf in Heqs; eauto.
            rewrite Heqs; cbn; auto.
            eapply addr_convert_safe_reverse; eauto.
          Qed.

          Lemma handle_gep_fin_inf :
            forall t base_addr_fin base_addr_inf idxs_fin idxs_inf res_addr_fin res_addr_inf,
              GEP.handle_gep t base_addr_fin idxs_fin = inr (NoOom res_addr_fin) ->
              dvalue_refine_strict base_addr_inf base_addr_fin ->
              dvalue_refine_strict res_addr_inf res_addr_fin ->
              map fin_to_inf_dvalue idxs_fin = idxs_inf ->
              IS1.LLVM.MEM.MP.GEP.handle_gep t base_addr_inf idxs_inf = inr (NoOom res_addr_inf).
          Proof.
            intros t base_addr_fin base_addr_inf idxs_fin idxs_inf res_addr_fin res_addr_inf H H0 H1 H2.

            unfold IS1.LLVM.MEM.MP.GEP.handle_gep, GEP.handle_gep in *.
            repeat break_match_hyp_inv.
            dvalue_refine_strict_inv H0; auto.
            dvalue_refine_strict_inv H1; auto.
            eapply handle_gep_addr_fin_inf in Heqs; eauto.
            rewrite Heqs; cbn; auto.
            eapply addr_convert_safe_reverse; eauto.
            eapply addr_convert_safe_reverse; eauto.
          Qed.

          - erewrite handle_gep_err_fin_inf; eauto.
            solve_orutt_raise.
            cbn.
            rewrite fin_to_inf_dvalue_iptr. congruence.
          - destruct o.
            2: {
              apply orutt_raise_oom.
            }
            erewrite handle_gep_fin_inf with (res_addr_inf:=fin_to_inf_dvalue d0); eauto.
            + apply orutt_Ret.
              apply fin_to_inf_dvalue_refine_strict.
            + apply fin_to_inf_dvalue_refine_strict.
            + cbn; rewrite fin_to_inf_dvalue_iptr. congruence.
        }

        intros ? ? ?.
        eapply orutt_bind with (RR:=Logic.eq).
        { apply orutt_trigger; cbn; eauto.
          - split; auto. split; auto.
            apply dvalue_refine_strict_dvalue_to_uvalue; auto.
          - intros [] [] REF; auto.
          - intros ? CONTRA; inv CONTRA.
        }

        intros [] [] _.
        apply orutt_trigger; cbn; eauto.
        intros [] [] _; auto.
        intros ? CONTRA; inv CONTRA.
    }

    { cbn.
      destruct instr; try solve_orutt_raise.
      - apply orutt_Ret; cbn; auto.
      - destruct fn.
        apply orutt_bind with (RR:=Forall2 uvalue_refine_strict).
        { apply map_monad_orutt.
          intros e0. destruct e0.
          apply translate_exp_to_instr_E1E2_orutt_strict.
          apply denote_exp_E1E2_orutt.
        }

        intros r1 r2 H.
        break_match_goal.
        { break_match_goal; [|break_match_goal; [|break_match_goal]].
          - (* va_start *)
            eapply orutt_bind with (RR:=uvalue_refine_strict).
            + destruct args; try solve_orutt_raise.
              destruct p, t.
              destruct args; try solve_orutt_raise.
              destruct varg1, varg2; inv VARG; try solve_orutt_raise.

              eapply orutt_bind with (RR:=uvalue_refine_strict).
              * apply translate_exp_to_instr_E1E2_orutt_strict.
                apply denote_exp_E1E2_orutt.
              * intros r0 r3 H0.
                eapply orutt_bind with (RR:=dvalue_refine_strict).
                eapply pickUnique_instr_E_orutt_strict; eauto.
                intros ? ? ?.
                destruct r5; dvalue_refine_strict_inv H2; try solve_orutt_raiseUB.
                all: try (apply orutt_bind with (RR:=Logic.eq);
                     [ apply orutt_trigger; cbn; eauto;
                       [ repeat split;
                         solve [ red; cbn;
                                 rewrite H2; auto
                               | red; cbn;
                                 rewrite H1; auto
                               | red; cbn;
                                 rewrite H3; auto
                               | eauto
                           ]
                       | intros [] [] ?; auto
                       | intros o CONTRA; inv CONTRA
                       ]
                     | intros ? ? ?;
                         apply orutt_Ret;
                       solve_uvalue_refine_strict
                       ]).
            + intros ? ? ?.
              apply orutt_Ret; eauto.
          - (* va_copy *)
            eapply orutt_bind with (RR:=uvalue_refine_strict).
            + destruct args; try solve_orutt_raise.
              destruct p, t.
              destruct args; try solve_orutt_raise.
              destruct d0; try solve_orutt_raise.
              destruct d0; try solve_orutt_raise.
              destruct p, t.
              destruct d0; try solve_orutt_raise.
              destruct args; try solve_orutt_raise.
              eapply orutt_bind with (RR:=uvalue_refine_strict).
              * apply translate_exp_to_instr_E1E2_orutt_strict.
                apply denote_exp_E1E2_orutt.
              * intros r0 r3 H0.
                eapply orutt_bind with (RR:=dvalue_refine_strict).
                eapply pickUnique_instr_E_orutt_strict; eauto.
                intros ? ? ?.
                eapply orutt_bind with (RR:=uvalue_refine_strict).
                { apply translate_exp_to_instr_E1E2_orutt_strict.
                  apply denote_exp_E1E2_orutt.
                }

                intros ? ? ?.
                eapply orutt_bind with (RR:=dvalue_refine_strict).
                eapply pickUnique_instr_E_orutt_strict; eauto.
                intros ? ? ?.
                eapply orutt_bind with (RR:=uvalue_refine_strict).
                { apply orutt_trigger; cbn; eauto.
                  intros t1 t2 H4.
                  apply H4.
                  intros ? CONTRA; inv CONTRA.
                }

                intros ? ? ?.
                eapply orutt_bind with (RR:=Logic.eq).
                { apply orutt_trigger; cbn; eauto.
                  intros [] [] ?; auto.
                  intros ? CONTRA; inv CONTRA.
                }

                intros [] [] _.
                apply orutt_Ret.
                solve_uvalue_refine_strict.
            + intros ? ? ?.
              apply orutt_Ret; auto.
          - (* va_end *)
            eapply orutt_bind with (RR:=uvalue_refine_strict).
            apply orutt_Ret; try solve_uvalue_refine_strict.
            intros ? ? ?.
            apply orutt_Ret; auto.
          - eapply orutt_bind with (RR:=uvalue_refine_strict).
            + eapply orutt_bind with (RR:=Forall2 dvalue_refine_strict).
              * eapply map_monad_orutt2; eauto.
                intros * ?.
                eapply pickUnique_instr_E_orutt_strict; eauto.
              * intros r0 r3 H0.
                eapply orutt_map.
                -- apply orutt_trigger; cbn; eauto.
                   ++ intros * ?.
                      apply H1.
                   ++ intros ? CONTRA.
                      inv CONTRA.
                -- intros r4 r5 H1.
                   cbn in *.
                   apply dvalue_refine_strict_dvalue_to_uvalue; eauto.
                   apply H1.
            + intros r0 r3 H0.
              eapply orutt_Ret; eauto.
        }

        apply orutt_bind with (RR:=uvalue_refine_strict).
        { - eapply orutt_bind with (RR:=uvalue_refine_strict).
            { apply translate_exp_to_instr_E1E2_orutt_strict.
              apply denote_exp_E1E2_orutt.
            }
            intros r0 r3 H0.

            eapply orutt_trigger; cbn; try tauto.
            intros o CONTRA.
            unfold subevent in CONTRA.
            inv CONTRA.
        }

        intros r0 r3 H0.
        apply orutt_Ret; eauto.
      - destruct val, ptr.
        apply orutt_bind with (RR:=uvalue_refine_strict).
        { apply translate_exp_to_instr_E1E2_orutt_strict.
          apply denote_exp_E1E2_orutt.
        }

        intros r1 r2 H.
        apply orutt_bind with (RR:=uvalue_refine_strict).
        { apply translate_exp_to_instr_E1E2_orutt_strict.
          apply denote_exp_E1E2_orutt.
        }

        intros r0 r3 H0.
        apply orutt_bind with (RR:=dvalue_refine_strict).
        { apply pickUnique_instr_E_orutt_strict; auto.
        }

        intros r4 r5 H1.
        { destruct r4; unfold dvalue_refine_strict; cbn in *; repeat break_match_hyp; inv H1; cbn;
            try
              solve
              [ apply orutt_trigger; cbn; auto;
                [ split; auto;
                  split; cbn; auto; solve_dvalue_refine_strict
                | intros [] [] _; auto
                | intros o CONTRA; inv CONTRA
                ]
              | solve_orutt_raiseUB
              | repeat break_match_hyp_inv;
                apply orutt_trigger; cbn; auto;
                [ split; auto;
                  split; auto; unfold dvalue_refine_strict; cbn; rewrite Heqo; auto
                | intros [] [] _; auto
                | intros o CONTRA; inv CONTRA]
              ].
        }

      - clear o.
        solve_orutt_raise.

      - (* va_arg *)
        break_match_goal; subst.
        eapply orutt_bind with (RR:=uvalue_refine_strict).
        { apply translate_exp_to_instr_E1E2_orutt_strict.
          apply denote_exp_E1E2_orutt.
        }

        intros ? ? ?.
        eapply orutt_bind.
        { apply pickUnique_instr_E_orutt_strict; auto.
        }

        intros ? ? ?.
        eapply orutt_bind with (RR:=uvalue_refine_strict).
        { apply orutt_trigger; cbn; eauto.
          intros ? ? REF; apply REF.
          intros ? CONTRA; inv CONTRA.
        }

        intros ? ? ?.
        eapply orutt_bind.
        { apply pickUnique_instr_E_orutt_strict; auto.
        }

        intros ? ? ?.
        eapply orutt_bind with (RR:=uvalue_refine_strict).
        { apply orutt_trigger; cbn; eauto.
          intros ? ? REF; apply REF.
          intros ? CONTRA; inv CONTRA.
        }

        intros ? ? ?.
        eapply orutt_bind with (RR:= fun a b => intptr_fin_inf b = a).
        { unfold lift_OOM.
          destruct (IP.from_Z 1) eqn:FROM.
          - pose proof intptr_convert_succeeds i as (?&?).
            erewrite IP.from_Z_to_Z in e0; eauto.
            rewrite e0.
            apply orutt_Ret.
            unfold intptr_fin_inf.
            break_match.
            clear Heqs.
            erewrite IP.from_Z_to_Z in e1; eauto.
            rewrite e0 in e1; inv e1; auto.
          - apply orutt_raise_oom.
        }

        intros ? ? IP_FIN_INF.
        eapply orutt_bind with (RR:=dvalue_refine_strict).
        { unfold lift_err_oom_RAISE_ERROR_OOM.
          destruct (GEP.handle_gep t r7 [DVALUE_IPTR r11]) eqn:GEP.
          - erewrite handle_gep_err_fin_inf; eauto.
            solve_orutt_raise.
            cbn.
            rewrite fin_to_inf_dvalue_iptr. congruence.
          - destruct o.
            2: {
              apply orutt_raise_oom.
            }
            erewrite handle_gep_fin_inf with (res_addr_inf:=fin_to_inf_dvalue d0); eauto.
            + apply orutt_Ret.
              apply fin_to_inf_dvalue_refine_strict.
            + apply fin_to_inf_dvalue_refine_strict.
            + cbn; rewrite fin_to_inf_dvalue_iptr. congruence.
        }

        intros ? ? ?.
        eapply orutt_bind with (RR:=Logic.eq).
        { apply orutt_trigger; cbn; eauto.
          - split; auto. split; auto.
            apply dvalue_refine_strict_dvalue_to_uvalue; auto.
          - intros [] [] REF; auto.
          - intros ? CONTRA; inv CONTRA.
        }

        intros [] [] _.
        apply orutt_Ret; auto.
    }
  Qed.

  Lemma dvalue_refine_strict_preserves_dvalue_is_poison :
    forall x y,
      dvalue_refine_strict x y ->
      DV1.dvalue_is_poison x = DV2.dvalue_is_poison y.
  Proof.
    intros x y H.
    destruct x;
      unfold dvalue_refine_strict in *; cbn in *; try break_match_hyp; inv H; cbn; auto.
  Qed.

  Lemma concretize_or_pick_exp_E_orutt_strict :
    forall uv1 uv2,
      uvalue_refine_strict uv1 uv2 ->
      orutt exp_E_refine_strict exp_E_res_refine_strict dvalue_refine_strict
        (IS1.LLVM.D.concretize_or_pick uv1) (concretize_or_pick uv2)
        (OOM:=OOME).
  Proof.
    intros uv1 uv2 REF.
    unfold IS1.LLVM.D.pickUnique, IS1.LLVM.D.concretize_or_pick.
    unfold pickUnique, concretize_or_pick.
    cbn.
    break_match;
      eapply uvalue_refine_strict_preserves_is_concrete with (uvc:=uv2) in Heqb; eauto;
      rewrite Heqb.

    apply lift_err_uvalue_to_dvalue_orutt_strict_exp_E; eauto.

    repeat rewrite bind_trigger.
    apply orutt_Vis.

    { cbn; auto. }

    intros t1 t2 H.
    apply orutt_Ret.
    destruct t1 as [dv1 []].
    destruct t2 as [dv2 []].
    cbn in *.
    inv H; subst_existT; cbn in *.
    tauto.

    intros o CONTRA; inv CONTRA.
  Qed.

  Lemma concretize_or_pick_L0'_orutt_strict :
    forall uv1 uv2,
      uvalue_refine_strict uv1 uv2 ->
      orutt L0'_refine_strict L0'_res_refine_strict dvalue_refine_strict
        (IS1.LLVM.D.concretize_or_pick uv1) (concretize_or_pick uv2)
        (OOM:=OOME).
  Proof.
    intros uv1 uv2 REF.
    unfold IS1.LLVM.D.pickUnique, IS1.LLVM.D.concretize_or_pick.
    unfold pickUnique, concretize_or_pick.
    cbn.
    break_match;
      eapply uvalue_refine_strict_preserves_is_concrete with (uvc:=uv2) in Heqb; eauto;
      rewrite Heqb.

    apply lift_err_uvalue_to_dvalue_orutt_strict_L0'; eauto.

    repeat rewrite bind_trigger.
    apply orutt_Vis.

    constructor; cbn; eauto.

    intros t1 t2 H.
    apply orutt_Ret.
    destruct t1 as [dv1 []].
    destruct t2 as [dv2 []].
    cbn in *.
    inv H; subst_existT; cbn in *.
    tauto.

    intros o CONTRA; inv CONTRA.
  Qed.

  Lemma denote_terminator_orutt_strict :
    forall term,
      orutt exp_E_refine_strict exp_E_res_refine_strict (sum_rel eq uvalue_refine_strict) (IS1.LLVM.D.denote_terminator term)
        (denote_terminator term)
        (OOM:=OOME).
  Proof.
    intros term.
    destruct term; cbn.
    - destruct v.
      eapply orutt_bind with (RR:=uvalue_refine_strict).
      apply denote_exp_E1E2_orutt.

      intros r1 r2 H.
      apply orutt_Ret; auto.
    - apply orutt_Ret; auto.
      constructor; solve_uvalue_refine_strict.
    - destruct v.
      eapply orutt_bind with (RR:=uvalue_refine_strict).
      apply denote_exp_E1E2_orutt.

      intros r1 r2 H.
      eapply orutt_bind with (RR:=dvalue_refine_strict).
      apply concretize_or_pick_exp_E_orutt_strict; eauto.

      intros r0 r3 H0.
      repeat break_match; unfold dvalue_refine_strict in *; cbn in *; try break_match_hyp; inv H0;
        try
          solve
          [ solve_orutt_raise
          | solve_orutt_raiseUB
          ];
        subst_existT;
        apply orutt_Ret; cbn; auto.
      rewrite Heqb in Heqb0; inv Heqb0.
      rewrite Heqb in Heqb0; inv Heqb0.
    - apply orutt_Ret; auto.
    - destruct v.
      eapply orutt_bind with (RR:=uvalue_refine_strict).
      apply denote_exp_E1E2_orutt.

      intros r1 r2 H.
      eapply orutt_bind with (RR:=dvalue_refine_strict).
      apply pickUnique_exp_E_orutt_strict; auto.

      intros r0 r3 H0.

      pose proof dvalue_refine_strict_preserves_dvalue_is_poison _ _ H0.
      rewrite H1.
      break_match;
        [solve_orutt_raiseUB|].

      eapply orutt_bind with (RR:=Forall2 (dvalue_refine_strict × eq)).
      { eapply map_monad_orutt.
        intros e0.
        destruct e0.
        destruct t.

        eapply orutt_bind with (RR:=dvalue_refine_strict).
        { repeat (break_match; try solve_orutt_raise).
          all: apply orutt_Ret; solve_dvalue_refine_strict.
        }

        intros r4 r5 H2.
        eapply orutt_Ret.
        constructor; auto.
      }

      (* TODO: Factor out this switch lemma *)
      { intros r4 r5 H2.
        induction H2.
        - cbn.
          apply orutt_Ret; auto.
        - cbn.
          destruct x, y.
          destruct r0;
            cbn in H1; inv H1;
            red in H0; cbn in H0;
            try break_match_hyp_inv; try inv H0;
            cbn; try solve_orutt_raise.
          + destruct H2; cbn in *; subst.
            destruct d0; red in fst_rel;
              cbn in fst_rel;
              subst;
              try break_match_hyp_inv; try inv fst_rel;
              cbn; try solve_orutt_raise.
            break_match_goal; subst; cbn; eauto;
              try solve_orutt_raise.
            break_match_goal; subst; cbn; eauto;
              apply orutt_Ret; auto.
      }
    - solve_orutt_raise.
    - solve_orutt_raise.
    - solve_orutt_raise.
    - solve_orutt_raiseUB.
  Qed.

  Lemma denote_block_orutt_strict :
    forall block bid varg1 varg2,
      OptionUtil.option_rel2 addr_refine varg1 varg2 ->
      orutt instr_E_refine_strict instr_E_res_refine_strict (sum_rel eq uvalue_refine_strict)
        (IS1.LLVM.D.denote_block block bid varg1)
        (denote_block block bid varg2)
        (OOM:=OOME).
  Proof.
    intros block bid varg1 varg2 VARG.
    cbn.
    apply orutt_bind with (RR:=eq).
    { apply denote_phis_orutt_strict. }

    intros [] [] _.
    apply orutt_bind with (RR:=eq).
    { apply orutt_bind with (RR:=Forall2 eq).
      { eapply map_monad_orutt.
        intros e.
        eapply denote_instr_orutt_strict; auto.
      }

      intros r1 r2 H.
      apply orutt_Ret.
      reflexivity.
    }

    intros [] [] _.
    apply translate_exp_to_instr_E1E2_orutt_strict.
    apply denote_terminator_orutt_strict.
  Qed.

  Lemma denote_ocfg_orutt_strict :
    forall cfg bids varg1 varg2,
      OptionUtil.option_rel2 addr_refine varg1 varg2 ->
      orutt instr_E_refine_strict instr_E_res_refine_strict (sum_rel (eq × eq) uvalue_refine_strict)
        (IS1.LLVM.D.denote_ocfg cfg varg1 bids)
        (denote_ocfg cfg varg2 bids)
        (OOM:=OOME).
  Proof.
    intros cfg [bid_from bid_src] varg1 varg2 VARG.
    Opaque denote_phis denote_phi.
    Opaque IS1.LLVM.D.denote_phis IS1.LLVM.D.denote_phi.
    unfold denote_ocfg, IS1.LLVM.D.denote_ocfg.
    cbn.
    eapply @orutt_iter_gen with (R:=eq); auto.
    intros x0 y0 EQ.
    subst.
    destruct y0 as [from src].

    break_match_goal.
    { (* Found a block *)
      eapply orutt_bind with (RR:=sum_rel eq uvalue_refine_strict).
      { eapply orutt_bind with (RR:=eq).
        { apply denote_phis_orutt_strict. }

        intros [] [] _.
        eapply orutt_bind with (RR:=eq).
        { eapply orutt_bind with (RR:=Forall2 eq).
          { eapply map_monad_orutt.
            intros e.
            eapply denote_instr_orutt_strict; auto.
          }

          intros r1 r2 H.
          apply orutt_Ret; auto.
        }

        intros [] [] _.
        apply translate_exp_to_instr_E1E2_orutt_strict.
        apply denote_terminator_orutt_strict.
      }

      intros r1 r2 H.
      inv H.
      apply orutt_Ret; auto.
      apply orutt_Ret; auto.
    }

    { (* No block found *)
      apply orutt_Ret.
      constructor.
      constructor.
      auto.
    }
  Qed.

  Lemma dtyp_of_uvalue_fun_fin_inf :
    forall uv_fin uv_inf,
      uvalue_refine_strict uv_inf uv_fin ->
      IS1.LP.Events.DV.dtyp_of_uvalue_fun uv_inf = dtyp_of_uvalue_fun uv_fin.
  Proof.
    intros uv_fin.
    induction uv_fin using uvalue_ind;
      intros uv_inf REF;
      uvalue_refine_strict_inv REF;
      try solve
        [ cbn; auto
        | cbn;
          erewrite IHuv_fin1; eauto;
          erewrite IHuv_fin2; eauto
        ].
    - apply map_monad_oom_Forall2 in H1.
      induction H1.
      + cbn; auto.
      + cbn.
        erewrite H; cbn; eauto.
        break_inner_match; auto.
        forward IHForall2.
        { intros u H2 uv_inf H3.
          apply H; cbn; eauto.
        }
        cbn in IHForall2.
        repeat break_match_hyp; inv IHForall2; auto.
    - apply map_monad_oom_Forall2 in H1.
      induction H1.
      + cbn; auto.
      + cbn.
        erewrite H; cbn; eauto.
        break_inner_match; auto.
        forward IHForall2.
        { intros u H2 uv_inf H3.
          apply H; cbn; eauto.
        }
        cbn in IHForall2.
        repeat break_match_hyp; inv IHForall2; auto.
    - apply map_monad_oom_Forall2 in H1.
      induction H1.
      + cbn; auto.
      + cbn.
        erewrite H; cbn; eauto.
        break_inner_match; auto.
        pose proof H1 as FORALL.
        apply Forall2_length in H1; subst.
        forward IHForall2.
        intros e H2 uv_inf H3.
        apply H; cbn; eauto.
        cbn in IHForall2.
        Transparent Datatypes.length.
        cbn.
        Opaque Datatypes.length.
        repeat break_match_goal;
          try congruence; exfalso.

        * invert_bools.
          rewrite <- H1, H2, H3 in Heqb0.
          cbn in Heqb0.
          rewrite <- H1, H4 in IHForall2.
          cbn in IHForall2.
          repeat break_match_hyp_inv.
          inv Heqb0.
          rewrite Bool.andb_true_r in Heqb0.
          clear Heqb1.
          apply dtyp_eqb_eq in H6; subst.

          (* TODO: Move this *)
          Lemma forallb_false :
            forall A (f : A -> bool) xs,
              forallb f xs = false ->
              exists x, In x xs /\ f x = false.
          Proof.
            intros A f xs.
            induction xs; intros FORALL.
            - inv FORALL.
            - cbn in FORALL.
              apply Bool.andb_false_iff in FORALL.
              destruct FORALL as [F | F].
              + exists a; cbn; auto.
              + specialize (IHxs F).
                destruct IHxs as (?&?&?).
                exists x; cbn; auto.
          Qed.

          apply forallb_false in Heqb0 as (?&?&?).
          erewrite <- H in H5; cbn; eauto.
          2: apply fin_to_inf_uvalue_refine_strict.
          eapply forallb_forall with (x:=(fin_to_inf_uvalue x0)) in H4.
          rewrite H4 in H5; discriminate.
          eapply Forall2_In_exists2 in FORALL; eauto.
          destruct FORALL as (?&?&?).
          erewrite <- fin_to_inf_uvalue_refine_strict'; eauto.
        * invert_bools.
          rewrite H1, H2, H3 in Heqb.
          cbn in Heqb.
          rewrite <- H1, H4 in IHForall2.
          cbn in IHForall2.
          rewrite Bool.andb_true_r in Heqb.
          repeat break_match_hyp_inv;
            rewrite Heqb in Heqb0.
          inv Heqb0.
          apply dtyp_eqb_eq in H6; subst.

          apply forallb_false in Heqb as (?&?&?).
          eapply Forall2_In in FORALL; eauto.
          destruct FORALL as (?&?&?).
          erewrite H in H5; cbn; eauto.
          eapply forallb_forall with (x:=x1) in H4; auto.
          rewrite H4 in H5; discriminate.
    - apply map_monad_oom_Forall2 in H1.
      induction H1.
      + cbn; auto.
      + cbn.
        erewrite H; cbn; eauto.
        break_inner_match; auto.
        pose proof H1 as FORALL.
        apply Forall2_length in H1; subst.
        forward IHForall2.
        intros e H2 uv_inf H3.
        apply H; cbn; eauto.
        cbn in IHForall2.
        Transparent Datatypes.length.
        cbn.
        Opaque Datatypes.length.
        repeat break_match_goal;
          try congruence; exfalso.

        * invert_bools.
          rewrite <- H1, H2, H3 in Heqb0.
          cbn in Heqb0.
          rewrite <- H1, H4 in IHForall2.
          cbn in IHForall2.
          repeat break_match_hyp_inv.
          inv Heqb0.
          rewrite Bool.andb_true_r in Heqb0.
          clear Heqb1.
          apply dtyp_eqb_eq in H6; subst.

          apply forallb_false in Heqb0 as (?&?&?).
          erewrite <- H in H5; cbn; eauto.
          2: apply fin_to_inf_uvalue_refine_strict.
          eapply forallb_forall with (x:=(fin_to_inf_uvalue x0)) in H4.
          rewrite H4 in H5; discriminate.
          eapply Forall2_In_exists2 in FORALL; eauto.
          destruct FORALL as (?&?&?).
          erewrite <- fin_to_inf_uvalue_refine_strict'; eauto.
        * invert_bools.
          rewrite <- H1, H2, H3 in Heqb0.
          cbn in Heqb0.
          rewrite <- H1, H4 in IHForall2.
          cbn in IHForall2.
          repeat break_match_hyp_inv.
          inv Heqb0.
          rewrite Bool.andb_true_r in Heqb0.
          clear Heqb1.
          apply dtyp_eqb_eq in H6; subst.

          apply forallb_false in Heqb0 as (?&?&?).
          erewrite <- H in H5; cbn; eauto.
          2: apply fin_to_inf_uvalue_refine_strict.
          eapply forallb_forall with (x:=(fin_to_inf_uvalue x0)) in H4.
          rewrite H4 in H5; discriminate.
          eapply Forall2_In_exists2 in FORALL; eauto.
          destruct FORALL as (?&?&?).
          erewrite <- fin_to_inf_uvalue_refine_strict'; eauto.
        * invert_bools.
          rewrite H1, H2, H3 in Heqb.
          cbn in Heqb.
          rewrite <- H1, H4 in IHForall2.
          cbn in IHForall2.
          rewrite Bool.andb_true_r in Heqb.
          repeat break_match_hyp_inv;
            rewrite Heqb in Heqb0.
          inv Heqb0.
          apply dtyp_eqb_eq in H6; subst.

          apply forallb_false in Heqb as (?&?&?).
          eapply Forall2_In in FORALL; eauto.
          destruct FORALL as (?&?&?).
          erewrite H in H5; cbn; eauto.
          eapply forallb_forall with (x:=x1) in H4; auto.
          rewrite H4 in H5; discriminate.
        * invert_bools.
          rewrite H1, H2, H3 in Heqb.
          cbn in Heqb.
          rewrite <- H1, H4 in IHForall2.
          cbn in IHForall2.
          rewrite Bool.andb_true_r in Heqb.
          repeat break_match_hyp_inv;
            rewrite Heqb in Heqb0.
          inv Heqb0.
          apply dtyp_eqb_eq in H6; subst.

          apply forallb_false in Heqb as (?&?&?).
          eapply Forall2_In in FORALL; eauto.
          destruct FORALL as (?&?&?).
          erewrite H in H5; cbn; eauto.
          eapply forallb_forall with (x:=x1) in H4; auto.
          rewrite H4 in H5; discriminate.
    - cbn.
      erewrite IHuv_fin; eauto.
    - cbn.
      erewrite IHuv_fin2; eauto.
      erewrite IHuv_fin1; eauto.
    - cbn.
      erewrite IHuv_fin3; eauto.
      erewrite IHuv_fin1; eauto.
      erewrite IHuv_fin2; eauto.
    - cbn.
      erewrite IHuv_fin3; eauto.
      erewrite IHuv_fin1; eauto.
      erewrite IHuv_fin2; eauto.
    - cbn.
      erewrite IHuv_fin; eauto.
    - cbn.
      erewrite IHuv_fin1; eauto.
      erewrite IHuv_fin2; eauto.
      erewrite IHuv_fin3; eauto.
    - apply map_monad_oom_Forall2 in H1.
      induction H1.
      + cbn; auto.
        rewrite sizeof_dtyp_fin_inf.
        auto.
      + cbn.
        rewrite sizeof_dtyp_fin_inf.
        pose proof H1 as FORALL.
        apply Forall2_length in H1; subst.
        forward IHForall2.
        intros e H2 uv_inf H3.
        apply H; cbn; eauto.
        cbn in IHForall2.
        Transparent Datatypes.length.
        cbn.
        Opaque Datatypes.length.
        repeat break_match_goal;
          try congruence; exfalso.

        * invert_bools.
          rewrite <- H1, H2 in Heqb0.
          cbn in Heqb0.
          destruct x; inv H3.
          cbn in H0.
          destruct (uvalue_convert_strict x) eqn:?; inv H0.
          cbn in Heqb0.
          rewrite <- H1, H4, Heqb0, sizeof_dtyp_fin_inf in IHForall2.
          destruct ((N.of_nat (Datatypes.length l) =? SIZEOF.sizeof_dtyp dt)%N); inv IHForall2.
          apply forallb_false in Heqb0 as (?&?&?).
          eapply Forall2_In_exists2 in FORALL; eauto.
          destruct FORALL as (?&?&?).
          eapply forallb_forall in H4; eauto.
          destruct x0; inv H3; uvalue_convert_strict_inv H6; discriminate.
        * invert_bools.
          rewrite H1, H2 in Heqb.
          cbn in Heqb.
          destruct y; inv H3.
          uvalue_convert_strict_inv H0.
          cbn in Heqb.
          apply forallb_false in Heqb as (?&?&?).
          eapply Forall2_In in FORALL; eauto.
          destruct FORALL as (?&?&?).
          eapply forallb_forall in H4; eauto.
          destruct x1; inv H4; uvalue_convert_strict_inv H7; discriminate.
  Qed.

  Lemma address_one_function_E1E2_orutt :
    forall dfn,
      orutt event_refine_strict event_res_refine_strict (eq × function_denotation_refine_strict)
        (LLVM1.address_one_function dfn)
        (LLVM2.address_one_function dfn)
        (OOM:=OOME).
  Proof.
    intros dfn.
    cbn.
    eapply orutt_bind with (RR:=dvalue_refine_strict).
    apply rutt_orutt. apply GlobalRead_L0_E1E2_rutt.
    solve_dec_oom.

    intros r1 r2 R1R2.
    destruct r2;
      dvalue_refine_strict_inv R1R2;
      try solve_orutt_raise.
    apply orutt_Ret.

    constructor.
    - cbn; auto.
      erewrite AC1.addr_convert_ptoi; eauto.
    - cbn.
      red.
      intros args1 args2 ARGS.
      cbn.
      eapply orutt_bind with (RR:=(Forall2 (eq × uvalue_refine_strict)) × Forall2 uvalue_refine_strict).
      { cbn.
        pose proof (Util.Forall2_length ARGS) as LEN.
        destruct (IS1.LLVM.D.combine_lists_varargs (LLVMAst.df_args dfn) args1) eqn:HARGS1.
        { (* Error, means args1 differs in length *)
          assert (combine_lists_varargs (LLVMAst.df_args dfn) args2 = inl s) as HARGS2.
          { clear - ARGS LEN HARGS1.
            remember (LLVMAst.df_args dfn) as names.
            clear Heqnames.
            generalize dependent args1.
            generalize dependent args2.
            induction names; intros args2 args1 ARGS LEN HARGS1; cbn in *.
            - induction ARGS; inv HARGS1.
            - induction ARGS; inv HARGS1; auto.
              break_match_hyp_inv.
              + erewrite IHnames; eauto.
              + destruct p; inv H2.
          }

          rewrite HARGS2.
          cbn.
          apply orutt_raise.
          intros ? ? CONTRA; inv CONTRA.
          repeat constructor.
        }

        {
          assert (exists p', combine_lists_varargs (LLVMAst.df_args dfn) args2 = inr p' /\ (Forall2 (eq × uvalue_refine_strict) × Forall2 uvalue_refine_strict) p p') as (p'&HARGS2&REF).
          { clear - ARGS LEN HARGS1.
            remember (LLVMAst.df_args dfn) as names.
            clear Heqnames.
            generalize dependent args1.
            generalize dependent args2.
            generalize dependent p.
            induction names; intros p args2 args1 ARGS LEN HARGS1; cbn in *.
            - induction ARGS; inv HARGS1.
              + exists ([], []).
                split; eauto.
              + exists ([], y :: l').
                split; eauto.
                constructor; cbn; auto.
            - induction ARGS; inv HARGS1; auto.
              break_match_hyp_inv.
              destruct p0; inv H2.
              assert (Datatypes.length l = Datatypes.length l') as LEN'.
              { inv LEN; auto. }

              pose proof (IHnames (l0, l1) l' l ARGS LEN' Heqs).
              destruct H0 as (?&?&?).
              destruct x0.
              exists ((a, y) :: l2, l3).
              rewrite H0.
              split; auto.
              inv H1; cbn in *.
              constructor; cbn; auto.
          }

          rewrite HARGS2.
          cbn.
          apply orutt_Ret; auto.
        }
      }

      cbn.
      intros [params1 vargs1] [params2 vargs2] [PARAMS VARGS].
      cbn in *.
      eapply orutt_bind with (RR:=eq).
      { unfold LLVMEvents.lift_err.
        induction VARGS.
        - cbn.
          apply orutt_Ret; auto.
        - cbn.
          erewrite dtyp_of_uvalue_fun_fin_inf; eauto.
          break_inner_match_goal.
          apply orutt_raise.
          intros ? ? CONTRA; inv CONTRA.
          repeat constructor.

          repeat break_inner_match_goal.
          + apply orutt_raise.
            intros ? ? CONTRA; inv CONTRA.
            repeat constructor.
          + pinversion IHVARGS.
          + pinversion IHVARGS.
          + apply orutt_Ret.
            apply orutt_inv_Ret in IHVARGS; subst; auto.
      }

      cbn.
      intros ? ? ?; subst.
      eapply orutt_bind with (RR:=eq).
      { apply orutt_trigger.
        cbn; auto.

        constructor.
        constructor.
        intros [] [] _.
        reflexivity.

        intros o CONTRA.
        inv CONTRA.
      }

      intros [] [] _.

      eapply orutt_bind with (RR:=eq).
      { apply orutt_trigger.
        - cbn.
          induction PARAMS.
          + constructor; cbn.
            apply local_refine_strict_empty.
          + destruct x0 as [xid xuv].
            destruct y as [yid yuv].
            inv H0.
            cbn in fst_rel, snd_rel. subst.
            constructor; cbn.
            inv IHPARAMS; subst_existT.
            apply alist_refine_cons; auto.
        - intros [] [] _.
          reflexivity.
        - intros o CONTRA; inv CONTRA.
      }

      intros [] [] _.
      eapply orutt_bind with (RR:=dvalue_refine_strict).
      { apply orutt_trigger.
        repeat constructor.
        intros ? ? ?.
        inv H0.
        subst_existT.
        inv H7.
        apply H1.
        intros ? CONTRA; inv CONTRA.
      }

      intros ? ? ?.
      eapply orutt_bind with (RR:=eq).
      { apply orutt_trigger.
        - cbn.
          repeat constructor; auto.
          red; cbn.
          induction VARGS; cbn; auto.
          rewrite H1.
          break_inner_match_goal; inv IHVARGS; auto.
        - intros [] [] _; auto.
        - intros ? CONTRA; inv CONTRA.
      }

      intros [] [] _.
      destruct r0; dvalue_refine_strict_inv H0;
        try solve [apply orutt_raise; [intros ? ? CONTRA; inv CONTRA|repeat constructor]].
      
      eapply orutt_bind with (RR:=uvalue_refine_strict).
      { rewrite translate_bind.
        rewrite translate_bind.

        eapply orutt_bind with (RR:=sum_rel (eq × eq) uvalue_refine_strict).
        { (* ocfg stuff *)
          apply translate_instr_to_L0'_E1E2_orutt_strict.
          apply denote_ocfg_orutt_strict.
          cbn.
          apply H0.
        }

        intros r0 r3 ?.
        inv H0.
        - inv H1.
          destruct a1, a2.
          cbn in *.
          subst.
          unfold LLVMEvents.raise.
          rewrite bind_trigger.
          rewrite bind_trigger.
          rewrite translate_vis.
          rewrite translate_vis.
          cbn.
          apply orutt_Vis; cbn; auto.
          constructor; cbn; auto.
          intros [] [] _.
          intros o CONTRA.
          inv CONTRA.
          do 2 rewrite translate_ret.
          apply orutt_Ret.
          auto.
      }

      intros r0 r3 R0R3.
      eapply orutt_bind with (RR:=eq).
      { eapply orutt_trigger.
        cbn; constructor; cbn; auto.
        intros [] [] _.
        reflexivity.
        intros o CONTRA; inv CONTRA.
      }

      intros [] [] _.
      eapply orutt_bind with (RR:=eq).
      { eapply orutt_trigger.
        cbn; constructor; cbn; auto.
        intros [] [] _.
        reflexivity.
        intros o CONTRA; inv CONTRA.
      }

      intros [] [] _.
      eapply orutt_Ret.
      auto.
  Qed.

  Lemma address_one_functions_E1E2_orutt :
    forall dfns,
      orutt event_refine_strict event_res_refine_strict
        (Forall2 (eq × function_denotation_refine_strict))
        (map_monad LLVM1.address_one_function dfns)
        (map_monad address_one_function dfns)
        (OOM:=OOME).
  Proof.
    intros dfns.
    apply map_monad_orutt.
    intros e.
    apply address_one_function_E1E2_orutt.
  Qed.

  Lemma lookup_defn_some_refine_strict :
    forall dfns1 dfns2 r1 r2 f_den1,
      IM_Refine function_denotation_refine_strict dfns1 dfns2 ->
      dvalue_refine_strict r1 r2 ->
      IS1.LLVM.D.lookup_defn r1 dfns1 = Some f_den1 ->
      exists f_den2,
        IS2.LLVM.D.lookup_defn r2 dfns2 = Some f_den2 /\
          function_denotation_refine_strict f_den1 f_den2.
  Proof.
    intros dfns1 dfns2 r1 r2 f_den1 [MEM DFNS] R1R2 LUP.

    unfold IS1.LLVM.D.lookup_defn in LUP.

    destruct r2;
      dvalue_refine_strict_inv R1R2; cbn in *;
      try discriminate.

    pose proof LUP as M.
    apply lookup_member in M.
    apply MEM in M.
    apply member_lookup in M.
    destruct M as (?&?).
    eapply DFNS in LUP; eauto.
    exists x0; split; eauto.
    erewrite <- AC1.addr_convert_ptoi; eauto.
  Qed.

  (* May not be true with new dvalue_refine *)
  Lemma lookup_defn_none_strict :
    forall dfns1 dfns2 r1 r2,
      IM_Refine function_denotation_refine_strict dfns1 dfns2 ->
      dvalue_refine_strict r1 r2 ->
      IS1.LLVM.D.lookup_defn r1 dfns1 = None ->
      IS2.LLVM.D.lookup_defn r2 dfns2 = None.
  Proof.
    intros dfns1 dfns2 r1 r2 [MEM LUP] REF L.
    unfold IS1.LLVM.D.lookup_defn in L.

    destruct r2;
      dvalue_refine_strict_inv REF; cbn in *;
      try auto.

    destruct (lookup (PTOI.ptr_to_int a) dfns2) eqn:L';
      auto.

    apply lookup_member in L'.
    apply MEM in L'.
    apply member_lookup in L' as (v&L').
    erewrite <- AC1.addr_convert_ptoi in L'; eauto.
    rewrite L in L'.
    discriminate.
  Qed.

  Lemma denote_mcfg_E1E2_orutt' :
    forall dfns1 dfns2 dt f1 f2 args1 args2,
      IM_Refine function_denotation_refine_strict dfns1 dfns2 ->
      (uvalue_refine_strict f1 f2) ->
      (Forall2 uvalue_refine_strict args1 args2) ->
      call_refine_strict IS1.LP.Events.DV.uvalue IS2.LP.Events.DV.uvalue (IS1.LP.Events.Call dt f1 args1) (Call dt f2 args2) ->
      orutt event_refine_strict event_res_refine_strict (fun res1 res2 => call_res_refine_strict IS1.LP.Events.DV.uvalue IS2.LP.Events.DV.uvalue (IS1.LP.Events.Call dt f1 args1) res1 (Call dt f2 args2) res2)
        (IS1.LLVM.D.denote_mcfg dfns1 dt f1 args1)
        (IS2.LLVM.D.denote_mcfg dfns2 dt f2 args2)
        (OOM:=OOME).
  Proof.
    intros dfns1 dfns2 dt f1 f2 args1 args2 DFNS F1F2 ARGS PRE12.
    unfold IS1.LLVM.D.denote_mcfg.
    unfold denote_mcfg.
    cbn in PRE12.
    destruct PRE12 as [DT [CONVf1f2 MAPM12]]; subst.

    eapply mrec_orutt with (RPreInv:=call_refine_strict).
    { intros A B d1 d2 PRE.

      cbn.
      destruct d1.
      destruct d2.

      cbn in PRE.

      eapply orutt_bind with (RR:=(fun r1 r2 => dvalue_refine_strict r1 r2)).
      { (* This may be tricky... *)
        (* Hopefully follows from uvalue_convert f = NoOom f0 in PRE *)
        unfold concretize_or_pick, IS1.LLVM.D.concretize_or_pick.
        destruct PRE as [T [UV ARGS_CONV]]; subst.

        break_match;
          eapply uvalue_refine_strict_preserves_is_concrete in Heqb;
          eauto; rewrite Heqb.
        - (* Concrete so just use uvalue_to_dvalue (simple) conversion *)
          apply rutt_orutt.
          apply lift_err_uvalue_to_dvalue_rutt_strict; auto.
          solve_dec_oom.
        - (* Not concrete, trigger pick events *)
          eapply orutt_bind with (RR:= fun (t1 : {_ : IS1.LP.Events.DV.dvalue | True}) (t2 : {_ : dvalue | True}) => dvalue_refine_strict (proj1_sig t1) (proj1_sig t2)) .
          { apply orutt_trigger.
            { constructor.
              cbn.
              tauto.
            }

            { intros t1 t2 H.
              inv H.
              cbn in *.
              apply inj_pair2 in H0, H3, H4, H5.
              subst.

              destruct t1 as [dv1 P1].
              destruct t2 as [dv2 P2].
              cbn in H6.
              cbn.
              tauto.
            }

            intros o CONTRA.
            inv CONTRA.
          }

          intros r1 r2 R1R2.
          apply orutt_Ret.
          destruct r1, r2.
          cbn in *.
          auto.
      }

      intros r1 r2 R1R2.
      (* Should be able to determine that the lookups
         are equivalent using DFNS *)
      cbn.
      break_match.
      { eapply lookup_defn_some_refine_strict in Heqo; eauto.
        destruct Heqo as (f_den2 & LUP2 & FDEN2).

        rewrite LUP2.
        red in FDEN2.
        specialize (FDEN2 args args0).
        forward FDEN2.
        { tauto.
        }

        destruct PRE as [T [CONV MAPM]]; subst.

        eapply orutt_weaken; eauto.
      }

      eapply lookup_defn_none_strict in Heqo; eauto.
      rewrite Heqo.

      eapply orutt_bind with (RR:=Forall2 dvalue_refine_strict).
      { (* Pick *)
        destruct PRE as [T [CONV MAPM]].
        induction MAPM.
        - cbn.
          apply orutt_Ret; auto.
        - do 2 rewrite map_monad_unfold.
          cbn.
          eapply orutt_bind with (RR:=dvalue_refine_strict).
          {
            apply pickUnique_orutt_strict; auto.
          }

          intros r0 r3 R0R3.
          eapply orutt_bind with (RR:=Forall2 dvalue_refine_strict);
            eauto.

          intros r4 r5 R4R5.
          eapply orutt_Ret.
          constructor; eauto.
      }

      intros r3 r4 R3R4.
      cbn.

      destruct PRE as [T [UV ARGS_CONV]]; subst.

      unfold ITree.map.
      eapply orutt_bind with (RR:=dvalue_refine_strict).
      {
        apply orutt_trigger.
        { constructor.
          cbn.
          split; split; auto.
        }

        intros t1 t2 H.
        inv H.
        cbn in *.
        apply inj_pair2 in H0, H3, H4, H5.
        subst.

        cbn in H6.
        tauto.

        intros o CONTRA.
        inv CONTRA.
      }

      intros r0 r5 R0R5.
      apply orutt_Ret.

      split; split; auto.
      split; auto.

      eapply dvalue_refine_strict_dvalue_to_uvalue; auto.
    }

    cbn. auto.
  Qed.

  Lemma denote_mcfg_E1E2_orutt'_orutt :
    forall dfns1 dfns2 dt f1 f2 args1 args2,
      orutt event_refine_strict event_res_refine_strict (fun res1 res2 => call_res_refine_strict IS1.LP.Events.DV.uvalue IS2.LP.Events.DV.uvalue (IS1.LP.Events.Call dt f1 args1) res1 (Call dt f2 args2) res2)
        (IS1.LLVM.D.denote_mcfg dfns1 dt f1 args1)
        (IS2.LLVM.D.denote_mcfg dfns2 dt f2 args2)
        (OOM:=OOME) ->
      orutt event_refine_strict event_res_refine_strict uvalue_refine_strict
        (IS1.LLVM.D.denote_mcfg dfns1 dt f1 args1)
        (IS2.LLVM.D.denote_mcfg dfns2 dt f2 args2)
        (OOM:=OOME).
  Proof.
    intros dfns1 dfns2 dt f1 f2 args1 args2 H.
    eapply orutt_weaken; eauto.
    intros r1 r2 H0.
    cbn in H0.
    tauto.
  Qed.

  Lemma denote_mcfg_E1E2_orutt :
    forall dfns1 dfns2 dt f1 f2 args1 args2,
      IM_Refine function_denotation_refine_strict dfns1 dfns2 ->
      (uvalue_refine_strict f1 f2) ->
      (Forall2 uvalue_refine_strict args1 args2) ->
      orutt event_refine_strict event_res_refine_strict uvalue_refine_strict
        (IS1.LLVM.D.denote_mcfg dfns1 dt f1 args1)
        (IS2.LLVM.D.denote_mcfg dfns2 dt f2 args2)
        (OOM:=OOME).
  Proof.
    intros dfns1 dfns2 dt f1 f2 args1 args2 H H0 H1.
    eapply denote_mcfg_E1E2_orutt'_orutt.
    eapply denote_mcfg_E1E2_orutt'; auto.
    cbn.
    split; auto.
  Qed.

  Lemma orutt_L0'_from_Z :
    forall ix,
      orutt (OOM:=OOME) L0'_refine_strict L0'_res_refine_strict
        (fun (ip_inf : IS1.LP.IP.intptr) (ip_fin : IP.intptr) => intptr_fin_inf ip_fin = ip_inf)
        (lift_OOM (IS1.LP.IP.from_Z ix)) (lift_OOM (IP.from_Z ix)).
  Proof.
    intros ix.
    unfold lift_OOM.
    destruct (IP.from_Z ix) eqn:HIX.
    2: {
      eapply orutt_raise_oom.
    }

    pose proof IP.from_Z_to_Z _ _ HIX.
    subst.
    pose proof (intptr_convert_succeeds i) as (?&?).
    rewrite e.
    eapply orutt_Ret.
    unfold intptr_fin_inf.
    break_match_goal.
    clear Heqs.
    rewrite e in e0.
    inv e0; auto.
  Qed.

  Lemma i8_str_index_refine :
    forall ix addr1 addr2,
      addr_refine addr1 addr2 ->
      orutt (OOM:=OOME) L0'_refine_strict L0'_res_refine_strict eq
        (LLVM1.i8_str_index addr1 ix) (LLVM2.i8_str_index addr2 ix).
  Proof.
    intros ix addr1 addr2 REF.
    unfold LLVM1.i8_str_index, LLVM2.i8_str_index.
    eapply orutt_bind with (RR:=fun ip_inf ip_fin => intptr_fin_inf ip_fin = ip_inf).
    { eapply orutt_L0'_from_Z. }

    intros r1 r2 R1R2.
    eapply orutt_bind with (RR:=addr_refine).
    { cbn.
      unfold intptr_fin_inf in R1R2.
      break_match_hyp.
      clear Heqs.
      subst.

      pose proof AC1.addr_convert_ptoi _ _ REF.
      rewrite H.
      rewrite sizeof_dtyp_fin_inf.
      assert (IS1.LP.IP.to_Z r1 = IP.to_Z r2).
      { eapply IS1.LP.IP.from_Z_to_Z in e.
        eauto.
      }

      (* Finite conversion *)
      destruct (ITOP.int_to_ptr (PTOI.ptr_to_int addr2 + Z.of_N (SIZEOF.sizeof_dtyp (DTYPE_I 8)) * IP.to_Z r2)
                  (PROV.address_provenance addr2)) eqn:HITOP.
      2: apply orutt_raiseOOM.

      cbn.

      pose proof addr_convert_succeeds addr2 as (?&?).
      pose proof addr_convert_succeeds a as (?&?).
      pose proof HITOP as HITOP'.
      eapply addr_convert_int_to_ptr in HITOP'; eauto.

      assert (IS1.LP.PROV.address_provenance x = IS1.LP.PROV.address_provenance addr1).
      { clear - e0 REF.
        pose proof addr_convert_safe _ _ e0.
        pose proof AC1.addr_convert_injective _ _ _ REF H; subst.
        reflexivity.
      }

      rewrite H1 in HITOP'.
      rewrite H0.
      rewrite HITOP'.

      cbn.
      eapply orutt_Ret.
      eapply addr_convert_safe; eauto.
    }

    intros r0 r3 H.
    eapply orutt_bind with (RR:=uvalue_refine_strict).
    { eapply orutt_trigger.
      - repeat constructor.
        rewrite dvalue_refine_strict_equation; cbn.
        rewrite H.
        reflexivity.
      - intros t1 t2 H0.
        repeat red in H0.
        inv H0; subst_existT.
        inv H7; subst_existT.
        destruct H1; auto.
      - intros o CONTRA; inv CONTRA.
    }

    intros r4 r5 H0.
    eapply orutt_bind with (RR:=dvalue_refine_strict).
    { eapply concretize_or_pick_L0'_orutt_strict; eauto. }

    intros r6 r7 H1.
    destruct r6; rewrite dvalue_refine_strict_equation in H1;
      cbn in H1; inv H1; repeat break_match_hyp_inv;
      try solve [eapply orutt_raise; [intros * CONTRA; inv CONTRA | constructor; constructor]].

    repeat break_match_goal;
        try solve [apply orutt_raise; [intros ? ? CONTRA; inv CONTRA|repeat constructor]].
    eapply orutt_Ret.
    reflexivity.
  Qed.

  Opaque LLVM1.i8_str_index.
  Opaque LLVM2.i8_str_index.

  Lemma puts_denotation_refine_strict_helper :
    forall r1 r2,
      dvalue_refine_strict r1 r2 ->
      orutt (OOM:=OOME) L0'_refine_strict L0'_res_refine_strict uvalue_refine_strict
        match r1 with
        | IS1.LP.Events.DV.DVALUE_Addr strptr =>
            ITree.bind (LLVM1.i8_str_index strptr 0)
              (fun (char : @Integers.int 8) =>
                 ITree.bind
                   (ITree.iter
                      (fun '(c, bytes, offset) =>
                         if @Integers.eq 8 c (@Integers.zero 8)
                         then Ret (inr ((@Integers.repr 8 10) :: bytes))
                         else
                           ITree.bind (LLVM1.i8_str_index strptr offset)
                             (fun (next_char : @Integers.int 8) => Ret (inl (next_char, c :: bytes, (offset + 1)%Z))))
                      (char, [], 1%Z))
                   (fun (bytes : list int8) =>
                      ITree.bind (trigger (IS1.LP.Events.IO_stdout (DList.rev_tail_rec bytes)))
                        (fun _ : unit => Ret (@IS1.LP.Events.DV.UVALUE_I 8 (@Integers.zero 8)))))
        | _ => raiseUB "puts got non-address argument"
        end
        match r2 with
        | DVALUE_Addr strptr =>
            ITree.bind (i8_str_index strptr 0)
              (fun (char : @Integers.int 8) =>
                 ITree.bind
                   (ITree.iter
                      (fun '(c, bytes, offset) =>
                         if @Integers.eq 8 c (@Integers.zero 8)
                         then Ret (inr (@Integers.repr 8 10 :: bytes))
                         else
                           ITree.bind (i8_str_index strptr offset)
                             (fun (next_char : @Integers.int 8) => Ret (inl (next_char, c :: bytes, (offset + 1)%Z))))
                      (char, [], 1%Z))
                   (fun bytes : list int8 =>
                      ITree.bind (trigger (IO_stdout (DList.rev_tail_rec bytes)))
                        (fun _ : unit => Ret (@UVALUE_I 8 Integers.zero))))
        | _ => raiseUB "puts got non-address argument"
        end.
  Proof.
    intros r1 r2 REF.
    destruct r1; rewrite dvalue_refine_strict_equation in REF; cbn in REF;
      inv REF; try break_match_hyp_inv;
      try solve [eapply orutt_raiseUB; [intros * CONTRA; inv CONTRA | constructor; constructor]].

    eapply orutt_bind with (RR:=eq).
    { eapply i8_str_index_refine; eauto. }

    intros r1 r2 R1R2; subst.
    eapply orutt_bind with (RR:=eq).
    { eapply orutt_iter' with (RI:=eq).
      2: reflexivity.

      intros j1 j2 H.
      subst.
      destruct j2 as ((?&?)&?).

      break_match_goal.
      { eapply orutt_Ret.
        constructor; reflexivity.
      }

      eapply orutt_bind with (RR:=eq).
      2: intros; subst; eapply orutt_Ret; constructor; reflexivity.
      eapply i8_str_index_refine; eauto.
    }

    intros r1 r0 H; subst.

    eapply orutt_bind with (RR:=eq).
    { eapply orutt_trigger.
      - repeat constructor.
      - intros [] [] ?.
        reflexivity.
      - intros o CONTRA; inv CONTRA.
    }

    intros [] [] _.
    eapply orutt_Ret.
    rewrite uvalue_refine_strict_equation.
    cbn.
    reflexivity.
  Qed.

  Lemma puts_denotation_refine_strict :
    function_denotation_refine_strict LLVM1.puts_denotation LLVM2.puts_denotation.
  Proof.
    red.
    intros args1 args2 ARGS.
    induction ARGS.
    - cbn.
      apply orutt_raise.
      + intros [] o CONTRA.
        inv CONTRA.
      + repeat red.
        constructor.
        cbn; auto.
    - destruct ARGS.
      2: {
        cbn.
        apply orutt_raise.
        + intros [] o CONTRA.
          inv CONTRA.
        + repeat red.
          constructor.
          cbn; auto.
      }
      destruct x;
        try solve
          [rewrite uvalue_refine_strict_equation in H;
           cbn in H; inv H;
           repeat break_match_hyp_inv;
           cbn;
           try solve
             [ setoid_rewrite bind_ret_l;
               eapply orutt_raiseUB; [intros * CONTRA; inv CONTRA | constructor; constructor]
             | eapply orutt_bind with (RR:=fun r1 r2 => dvalue_refine_strict r1 r2);
               [ eapply concretize_or_pick_L0'_orutt_strict;
                 rewrite uvalue_refine_strict_equation;
                 cbn;
                 rewrite Heqo;
                 reflexivity
               | intros *;
                 eapply puts_denotation_refine_strict_helper; eauto
               ]
             | eapply orutt_bind with (RR:=fun r1 r2 => dvalue_refine_strict r1 r2);
               [ eapply orutt_bind with (RR:=fun r1 r2 => dvalue_refine_strict (proj1_sig r1) (proj1_sig r2))|];
               [ eapply orutt_trigger;
                 [ repeat constructor;
                   cbn;
                   rewrite uvalue_refine_strict_equation;
                   cbn;
                   try rewrite Heqo;
                   try rewrite Heqo0;
                   try rewrite Heqo1;
                   reflexivity
                 | intros * REF;
                   destruct t1, t2; cbn in *;
                   inv REF; subst_existT;
                   inv H5; subst_existT; eauto
                 | intros * CONTRA; inv CONTRA
                 ]
               | intros [r1 ?] [r2 ?] REF;
                 eapply orutt_Ret; eauto
               | intros r1 r2 REF;
                 eapply puts_denotation_refine_strict_helper; eauto
               ]
             ]
          ].

      rewrite uvalue_refine_strict_equation in H;
        cbn in H; inv H;
        repeat break_match_hyp_inv;
        cbn.
      repeat rewrite bind_ret_l.

      eapply orutt_bind with (RR:=eq).
      { eapply i8_str_index_refine; eauto. }

      intros ? ? ?; subst.
      eapply orutt_bind with (RR:=eq).
      { eapply orutt_iter' with (RI:=eq).
        2: reflexivity.

        intros j1 j2 H.
        subst.
        destruct j2 as ((?&?)&?).

        break_match_goal.
        { eapply orutt_Ret.
          constructor; reflexivity.
        }

        eapply orutt_bind with (RR:=eq).
        2: intros; subst; eapply orutt_Ret; constructor; reflexivity.
        eapply i8_str_index_refine; eauto.
      }

      intros ? ? ?; subst.
      eapply orutt_bind with (RR:=eq).
      eapply orutt_trigger;
        [ repeat constructor;
          cbn;
          rewrite uvalue_refine_strict_equation;
          cbn;
          try rewrite Heqo;
          try rewrite Heqo0;
          try rewrite Heqo1;
          reflexivity
        | intros * REF;
          destruct t1, t2; cbn in *;
          inv REF; subst_existT;
          inv H5; subst_existT; eauto
        | intros * CONTRA; inv CONTRA
        ].

      intros [] [] _.
      eapply orutt_Ret.
      rewrite uvalue_refine_strict_equation; cbn; eauto.
  Qed.

  (* TODO: Move these *)
  Hint Resolve orutt_bind orutt_Ret orutt_trigger orutt_raise orutt_raiseUB orutt_raiseOOM: ORUTT.
  Hint Extern 1 (uvalue_refine_strict _ _) => solve_uvalue_refine_strict : ORUTT.
  Hint Extern 1 (dvalue_refine_strict _ _) => solve_dvalue_refine_strict : ORUTT.


  Opaque Pos.eq_dec.

  Lemma putchar_denotation_refine_strict :
    function_denotation_refine_strict LLVM1.putchar_denotation LLVM2.putchar_denotation.
  Proof.
    red.
    intros args1 args2 ARGS.
    induction ARGS.
    - cbn.
      apply orutt_raise.
      + intros [] o CONTRA.
        inv CONTRA.
      + repeat red.
        constructor.
        cbn; auto.
    - destruct ARGS.
      2: {
        cbn.
        apply orutt_raise.
        + intros [] o CONTRA.
          inv CONTRA.
        + repeat red.
          constructor.
          cbn; auto.
      }

      destruct y; uvalue_refine_strict_inv H.
      all:
        try solve
          [ eapply orutt_bind with (RR:=dvalue_refine_strict);
            solve [ eapply orutt_bind with (RR:=fun r1 r2 => dvalue_refine_strict (proj1_sig r1) (proj1_sig r2));
                    [ apply orutt_trigger;
                      [ repeat constructor; cbn;
                        rewrite uvalue_refine_strict_equation; cbn;
                        try rewrite H0; try rewrite H1; try rewrite H2; reflexivity
                      | intros [dv1 []] [dv2 []] REF;
                        inv REF; subst_existT; cbn;
                        match goal with
                        | H: event_res_refine_strict _ _ _ _ _ _ |- _ =>
                            apply H
                        end
                      | intros ? CONTRA; inv CONTRA
                      ]
                    | intros [dv1 []] [dv2 []] REF;
                      eapply orutt_Ret; eauto; solve_uvalue_refine_strict
                    ]
                  | intros r1 r2 REF;
                    destruct r2; dvalue_refine_strict_inv REF;
                    try destruct (Pos.eq_dec 32 sz);
                    try (eapply orutt_raiseUB;
                         [ intros ? ? CONTRA; inv CONTRA
                         | repeat constructor
                      ]);
                    eapply orutt_bind with (RR:=eq); subst; cbn; eauto with ORUTT;
                    break_match; try contradiction; subst; cbn;
                    dependent destruction e; cbn;
                    eapply orutt_trigger; eauto with ORUTT;
                    [ repeat constructor
                    | intros [] [] ?; reflexivity
                    | intros ? CONTRA; inv CONTRA
                    ]
                  | cbn;
                    eapply concretize_or_pick_L0'_orutt_strict;
                    rewrite uvalue_refine_strict_equation; cbn; rewrite H0; reflexivity
              ]
          ].

      all:
        try solve [ cbn;
                    setoid_rewrite bind_ret_l;
                    eapply orutt_raiseUB; [intros * CONTRA; inv CONTRA | constructor; constructor]
          ].

      cbn.
      repeat rewrite bind_ret_l.
      break_match_goal; subst; cbn;
        try solve [eapply orutt_raiseUB; [intros * CONTRA; inv CONTRA | constructor; constructor]].

      break_match_goal; subst; try contradiction; cbn.
      dependent destruction e; cbn.
      eapply orutt_bind with (RR:=eq); eauto with ORUTT.
      { apply orutt_trigger;
          [ solve [repeat constructor]
          | intros [] [] ?; reflexivity
          | intros ? CONTRA; inv CONTRA
          ].
      }
  Qed.

  Lemma address_one_builtin_functions_E1E2_orutt :
    forall dfns1 dfns2,
      Forall2 (eq × function_denotation_refine_strict) dfns1 dfns2 ->
      orutt event_refine_strict event_res_refine_strict
        (Forall2 (eq × function_denotation_refine_strict))
        (map_monad LLVM1.address_one_builtin_function dfns1)
        (map_monad address_one_builtin_function dfns2)
        (OOM:=OOME).
  Proof.
    intros dfns1 dfns2 EQV.
    eapply map_monad_orutt2 with (VV:=prod_rel eq function_denotation_refine_strict); eauto.
    intros [id1 f1] [id2 f2] EQV'.
    inv EQV'.
    cbn in *; subst.
    eapply orutt_bind with (RR:=dvalue_refine_strict).
    { eapply rutt_orutt.
      apply GlobalRead_L0_E1E2_rutt.
      intros A e2.
      apply L0_dec_oom.
    }

    intros r1 r2 H.
    destruct r2;
      dvalue_refine_strict_inv H; cbn in *;
      try solve_orutt_raise.
    eapply orutt_Ret.
    constructor; eauto.
    cbn.
    erewrite <- AC1.addr_convert_ptoi; eauto.
  Qed.

  Lemma builtins_refine_strict :
    forall decs,
      Forall2 (eq × function_denotation_refine_strict)
        (LLVM1.built_in_functions decs)
        (built_in_functions decs).
  Proof.
    intros decs.
    induction decs.
    - cbn; constructor.
    - unfold built_in_functions.
      unfold LLVM1.built_in_functions.
      cbn.

      (* puts *)
      break_match_goal; try constructor; eauto.
      constructor; cbn; auto.
      apply puts_denotation_refine_strict.

      (* putchar *)
      break_match_goal; try constructor; eauto.
      constructor; cbn; auto.
      apply putchar_denotation_refine_strict.

      break_match_goal; try constructor; eauto.
      constructor; eauto.
      cbn.
      apply putchar_denotation_refine_strict.
  Qed.

  Lemma model_E1E2_L0_orutt_strict_sound
    (p : list
           (LLVMAst.toplevel_entity
              LLVMAst.typ
              (LLVMAst.block LLVMAst.typ * list (LLVMAst.block LLVMAst.typ)))) :
    model_E1E2_L0_orutt_strict p p.
  Proof.
    red.

    unfold denote_vellvm.
    unfold LLVM1.denote_vellvm.
    eapply orutt_bind; [apply build_global_environment_E1E2_orutt_strict_sound|].

    intros [] [] _.
    eapply orutt_bind; [apply address_one_functions_E1E2_orutt|].

    intros r1' r2' R1R2'.
    eapply orutt_bind; [apply address_one_builtin_functions_E1E2_orutt; apply builtins_refine_strict|].

    intros r1 r2 R1R2.
    eapply orutt_bind;
      [apply rutt_orutt;
       [try apply GlobalRead_L0_E1E2_rutt | solve_dec_oom]|].

    intros r3 r4 R3R4.
    eapply orutt_bind.

    { apply denote_mcfg_E1E2_orutt; auto.
      - apply IM_Refine_of_list_app; eauto.
      - apply dvalue_refine_strict_dvalue_to_uvalue; auto.
      - (* TODO: fold into main_args lemma probably *)
        unfold main_args.
        unfold LLVM1.main_args.
        constructor.
        + unfold uvalue_refine_strict.
          reflexivity.
        + constructor; [|constructor].
          unfold uvalue_refine_strict.
          cbn.
          rewrite AC1.addr_convert_null.
          reflexivity.
    }

    intros r0 r5 H.
    eapply orutt_bind with (RR:=fun x y => dvalue_refine_strict (proj1_sig x) (proj1_sig y)).
    { (* Pick *)
      apply orutt_trigger.
      { cbn; auto.
      }

      intros t1 t2 H0.
      cbn in *.
      destruct t1, t2; tauto.
      intros o CONTRA; inv CONTRA.
    }

    intros r6 r7 H0.
    cbn.
    apply orutt_Ret; auto.
  Qed.

  Lemma E1E2_interp_global_orutt_strict :
    forall t1 t2 g1 g2,
      L0_E1E2_orutt_strict t1 t2 ->
      global_refine_strict g1 g2 ->
      L1_E1E2_orutt_strict (interp_global t1 g1) (interp_global t2 g2).
  Proof.
    intros t1 t2 g1 g2 RL0 GENVS.
    unfold interp_global.
    unfold State.interp_state.
    red.
    red in RL0.

    Set Nested Proofs Allowed.
    Lemma orutt_interp :
      forall {E1 E2 F1 F2 OOM1 OOME1 OOM2 OOME2 R1 R2 pre1 post1 pre2 post2 RR}
        (h1 : forall T, E1 T -> itree F1 T)
        (h2 : forall T, E2 T -> itree F2 T)
        t1 t2,
        @orutt E1 E2 OOM1 OOME1 R1 R2 pre1 post1 RR t1 t2 ->
        (forall A B e1 e2,
            pre1 A B e1 e2 ->
            @orutt F1 F2 OOM2 OOME2 A B pre2 post2 (fun a b => post1 A B e1 a e2 b) (h1 A e1) (h2 B e2)) ->
        (* OOM Spec... Probably too strong right now, but easier to rewrite this way. *)
        (forall A (o : OOM1 A), exists (o' : OOM2 A) k, h2 A (subevent A o) = (vis o' k)) ->
        @orutt F1 F2 OOM2 OOME2 R1 R2 pre2 post2 RR (interp h1 t1) (interp h2 t2).
    Proof.
      intros E1 E2 F1 F2 OOM1 OOME1 OOM2 OOME2 R1 R2 pre1 post1 pre2 post2 RR h1 h2 t1 t2 EQ HANDLER OOMSPEC.
      revert EQ. revert t1 t2.
      ginit. gcofix CIH.
      intros t1 t2 EQ.
      punfold EQ; red in EQ.
      dependent induction EQ; subst; setoid_rewrite unfold_interp.
      - rewrite <- x, <- x0.
        cbn; gstep; red; cbn.
        constructor; auto.
      - rewrite <- x, <- x0.
        cbn; gstep; red; cbn.
        constructor; auto.
        gbase; pclearbot.
        eapply CIH; eauto.
      - rename H0 into KEQ.
        (* KEQ may be what I need to relate the continuations after the handler *)
        (* I may need to know something about how pre1 / pre2 and post1 / post2 relate to each other *)
        pose proof H as HSPEC.
        apply HANDLER in HSPEC.
        punfold HSPEC; red in HSPEC.
        revert HSPEC.
        gcofix CIH2.
        intros HSPEC.
        dependent induction HSPEC.
        + cbn in *.
          rewrite <- x0, <- x1.
          cbn. do 2 rewrite unfold_bind.
          rewrite <- x, <- x2.
          gstep; red; cbn.
          constructor.
          gbase.
          eapply CIH; eauto.
          specialize (KEQ _ _ H0).
          pclearbot.
          eauto.
        + cbn in *.
          rewrite <- x0, <- x1.
          cbn. do 2 rewrite unfold_bind.
          rewrite <- x, <- x2.
          gstep; red; cbn.
          constructor.
          pclearbot.
          eapply gpaco2_uclo; [|eapply orutt_clo_bind|]; eauto with paco.
          econstructor; eauto. intros ? ? ?.
          * gstep.
            red; cbn.
            constructor.
            gbase.
            eapply CIH; eauto.
            cbn in *.
            apply KEQ in H2.
            pclearbot.
            eauto.
        + cbn in *.
          rewrite <- x0, <- x1.
          cbn. do 2 rewrite unfold_bind.
          rewrite <- x, <- x2.
          gstep; red; cbn.
          constructor; eauto.
          intros a b H8.
          eapply gpaco2_uclo; [|eapply orutt_clo_bind|]; eauto with paco.
          econstructor; eauto.

          apply H0 in H8.
          pclearbot.
          eauto.

          intros u1 u2 H9.
          cbn in *.
          gstep; red; cbn.
          constructor; eauto.
          gbase.
          eapply CIH; eauto.
          apply KEQ in H9.
          pclearbot; eauto.
        + (* OOM *)
          cbn in *.
          rewrite <- x0, <- x1.
          cbn. do 2 rewrite unfold_bind.
          rewrite <- x.
          gstep; red; cbn.
          constructor.
        + (* TauL *)
          cbn in *.
          rewrite <- x0, <- x1.
          eapply gpaco2_uclo; [|eapply orutt_clo_bind|]; eauto with paco.
          econstructor; eauto. intros ? ? ?.
          * gstep.
            red; cbn.
            constructor.
            gbase.
            eapply CIH; eauto.
            cbn in *.
            apply KEQ in H0.
            pclearbot.
            eauto.
        + (* TauR *)
          cbn in *.
          rewrite <- x0, <- x1.
          eapply gpaco2_uclo; [|eapply orutt_clo_bind|]; eauto with paco.
          econstructor; eauto. intros ? ? ?.
          * gstep.
            red; cbn.
            constructor.
            gbase.
            eapply CIH; eauto.
            cbn in *.
            apply KEQ in H0.
            pclearbot.
            eauto.
      - (* OOM *)
        specialize (OOMSPEC _ e).
        destruct OOMSPEC as [o' [k OOMEQ]].
        rewrite <- x.
        cbn.
        rewrite OOMEQ.
        rewrite bind_vis.
        gstep; red; cbn.
        constructor.
      - (* TauL *)
        cbn in *.
        rewrite <- x.
        cbn.
        rewrite tau_euttge.
        rewrite <- unfold_interp.
        eapply IHEQ; eauto.
      - (* TauR *)
        cbn in *.
        rewrite <- x.
        cbn.
        rewrite tau_euttge.
        rewrite <- unfold_interp.
        eapply IHEQ; eauto.
    Qed.

    Set Nested Proofs Allowed.
    Lemma orutt_interp_state :
      forall {E1 E2 F1 F2 OOM1 OOME1 OOM2 OOME2 R1 R2 RR S1 S2}
        {SS : S1 -> S2 -> Prop}
        {pre1 : prerel E1 E2} {post1 : postrel E1 E2} {pre2 : prerel F1 F2} {post2 : postrel F1 F2}
        (h1 : forall T, E1 T -> Monads.stateT S1 (itree F1) T)
        (h2 : forall T, E2 T -> Monads.stateT S2 (itree F2) T)
        t1 t2 s1 s2,
        @orutt E1 E2 OOM1 OOME1 R1 R2 pre1 post1 RR t1 t2 ->
        SS s1 s2 ->
        (forall A B e1 e2 s1 s2,
            pre1 A B e1 e2 ->
            SS s1 s2 ->
            @orutt F1 F2 OOM2 OOME2 (S1 * A)%type (S2 * B)%type pre2 post2 (fun '(s1, a) '(s2, b) => post1 A B e1 a e2 b /\ SS s1 s2) (h1 A e1 s1) (h2 B e2 s2)) ->
        (* OOM Spec... *)
        (forall A (o : OOM1 A) s, exists (o' : OOM2 A) k, h2 A (subevent A o) s ≈ (vis o' k)) ->
        @orutt F1 F2 OOM2 OOME2 (S1 * R1)%type (S2 * R2)%type pre2 post2 (SS × RR) (State.interp_state h1 t1 s1) (State.interp_state h2 t2 s2).
    Proof.
      intros E1 E2 F1 F2 OOM1 OOME1 OOM2 OOME2 R1 R2 RR S1 S2 SS pre1 post1 pre2 post2 h1 h2 t1 t2 s1 s2 EQ SSINIT HANDLER OOMSPEC.
      revert EQ SSINIT. revert t1 t2 s1 s2.
      ginit. gcofix CIH.
      intros t1 t2 s1 s2 EQ SSINIT.
      punfold EQ; red in EQ.
      dependent induction EQ; subst; setoid_rewrite StateFacts.unfold_interp_state.
      - rewrite <- x, <- x0.
        cbn; gstep; red; cbn.
        constructor; constructor; cbn; auto.
      - rewrite <- x, <- x0.
        cbn; gstep; red; cbn.
        constructor; auto.
        gbase; pclearbot.
        eapply CIH; eauto.
      - rename H0 into KEQ.
        (* KEQ may be what I need to relate the continuations after the handler *)
        (* I may need to know something about how pre1 / pre2 and post1 / post2 relate to each other *)
        pose proof H as HSPEC.
        eapply HANDLER in HSPEC; eauto.
        punfold HSPEC; red in HSPEC.
        revert HSPEC.
        gcofix CIH2.
        intros HSPEC.
        dependent induction HSPEC.
        + cbn in *.
          rewrite <- x0, <- x1.
          cbn. do 2 rewrite unfold_bind.
          rewrite <- x, <- x2.
          gstep; red; cbn.
          constructor.
          gbase.
          destruct r1, r2.
          destruct H0.
          eapply CIH; eauto.
          specialize (KEQ _ _ H0).
          pclearbot.
          eauto.
        + cbn in *.
          rewrite <- x0, <- x1.
          cbn. do 2 rewrite unfold_bind.
          rewrite <- x, <- x2.
          gstep; red; cbn.
          constructor.
          pclearbot.
          eapply gpaco2_uclo; [|eapply orutt_clo_bind|]; eauto with paco.
          econstructor; eauto. intros ? ? ?.
          * gstep.
            red; cbn.
            constructor.
            gbase.
            destruct u1, u2, H2.
            eapply CIH; eauto.
            cbn in *.
            apply KEQ in H2.
            pclearbot.
            eauto.
        + cbn in *.
          rewrite <- x0, <- x1.
          cbn. do 2 rewrite unfold_bind.
          rewrite <- x, <- x2.
          gstep; red; cbn.
          constructor; eauto.
          intros a b H8.
          eapply gpaco2_uclo; [|eapply orutt_clo_bind|]; eauto with paco.
          econstructor; eauto.

          apply H0 in H8.
          pclearbot.
          eauto.

          intros u1 u2 H9.
          cbn in *.
          gstep; red; cbn.
          constructor; eauto.
          gbase.
          destruct u1, u2, H9.
          eapply CIH; eauto.
          eapply KEQ in H4; eauto.
          pclearbot; eauto.
        + (* OOM *)
          cbn in *.
          rewrite <- x0, <- x1.
          cbn. do 2 rewrite unfold_bind.
          rewrite <- x.
          gstep; red; cbn.
          constructor.
        + (* TauL *)
          cbn in *.
          rewrite <- x0, <- x1.
          eapply gpaco2_uclo; [|eapply orutt_clo_bind|]; eauto with paco.
          econstructor; eauto. intros ? ? ?.
          * gstep.
            red; cbn.
            constructor.
            gbase.
            destruct u1, u2, H0; cbn in *.
            eapply CIH; eauto.
            cbn in *.
            apply KEQ in H0.
            pclearbot.
            eauto.
        + (* TauR *)
          cbn in *.
          rewrite <- x0, <- x1.
          eapply gpaco2_uclo; [|eapply orutt_clo_bind|]; eauto with paco.
          econstructor; eauto. intros ? ? ?.
          * gstep.
            red; cbn.
            constructor.
            gbase.
            destruct u1, u2, H0.
            eapply CIH; eauto.
            cbn in *.
            apply KEQ in H0.
            pclearbot.
            eauto.
      - (* OOM *)
        specialize (OOMSPEC _ e s2).
        destruct OOMSPEC as [o' [k OOMEQ]].
        rewrite <- x.
        cbn.

        eapply gpaco2_final.
        apply orutt_monot.
        right.

        eapply paco2_mon_bot; eauto.
        eapply orutt_cong_eutt2.
        2: {
          rewrite OOMEQ.
          rewrite bind_vis.
          cbn.
          reflexivity.
        }

        pstep; red; cbn.
        constructor.
      - (* TauL *)
        cbn in *.
        rewrite <- x.
        cbn.
        rewrite tau_euttge.
        rewrite <- StateFacts.unfold_interp_state.
        eapply IHEQ; eauto.
      - (* TauR *)
        cbn in *.
        rewrite <- x.
        cbn.
        rewrite tau_euttge.
        rewrite <- StateFacts.unfold_interp_state.
        eapply IHEQ; eauto.
    Qed.

    Lemma orutt_interp_global_h :
      forall A B e1 e2 genv1 genv2,
        event_refine_strict A B e1 e2 ->
        global_refine_strict genv1 genv2 ->
        orutt L1_refine_strict L1_res_refine_strict
          (fun '(s0, a) '(s3, b) => event_res_refine_strict A B e1 a e2 b /\ global_refine_strict s0 s3)
          (interp_global_h e1 genv1) (interp_global_h e2 genv2)
          (OOM:=OOME).
    Proof.
    intros A B e1 e2 genv1 genv2 REF GREF.
    destruct e1; repeat (destruct e); repeat (destruct s);
    try
      solve
        [
          cbn in REF;
          destruct e2; try inv REF;
          repeat (break_match_hyp; try inv REF);
          cbn in *;
          pstep; red; cbn;
          constructor; cbn; auto;
          [ intros ? ? ?;
              left;
            pstep; red; cbn;
            constructor; auto
          | intros o CONTRA; inv CONTRA
          ]
        ].

    all: try
           solve
           [ cbn in REF;
             destruct e2; try inv REF;
             repeat (break_match_hyp; try inv REF);
             cbn in *;
             (pstep; red; cbn;
              constructor; cbn; try tauto;
              [ intros ? ? ?; left; apply orutt_Ret; tauto
              | intros o CONTRA; inv CONTRA
             ])
           |
             cbn in REF;
             destruct e2; try inv REF;
             repeat (break_match_hyp; try inv REF);
             cbn in *;
             (pstep; red; cbn;
              constructor; cbn;
              [ first [red; red; auto | tauto]
              | intros ? ? ?; left; apply orutt_Ret; tauto
              | intros o CONTRA; inv CONTRA
             ])
           ].

    -
      cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF).
      + cbn in *.
        apply orutt_Ret.
        split; auto.
        apply global_refine_strict_add; auto.

      + cbn.
        pose proof GREF as GREF'.
        do 2 red in GREF.
        specialize (GREF id0).
        red in GREF.
        break_match_goal.
        { (* Found id in genv *)
          break_match_goal; try contradiction.
          apply orutt_Ret.
          split; eauto.
        }

        { (* Id not found in genv *)
          break_match_goal; try contradiction.
          solve_orutt_raise.
        }
    - cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF).

      { cbn.
        apply orutt_bind with (RR:=eq).
        apply orutt_trigger; cbn; eauto.
        intros [] [] _; auto.
        intros o CONTRA; inv CONTRA.
        intros [] [] _.
        apply orutt_Ret; tauto.
      }

      { cbn.
        apply orutt_bind with (RR:=uvalue_refine_strict).
        apply orutt_trigger; cbn; eauto.
        intros x y [_ REFxy]; auto.
        intros o CONTRA; inv CONTRA.
        intros r1 r2 REFr1r2.
        apply orutt_Ret; tauto.
      }
    - cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF).

       { cbn.
         apply orutt_bind with (RR:=eq).
         { apply orutt_trigger; cbn; eauto.
           intros [] [] _; auto.
           intros o CONTRA; inv CONTRA.
         }
         intros [] [] _.
         apply orutt_Ret; split; auto.
      }

       { cbn.
         apply orutt_bind with (RR:=eq).
         { apply orutt_trigger; cbn; eauto.
           intros [] [] _; auto.
           intros o CONTRA; inv CONTRA.
         }
         intros [] [] _.
         apply orutt_Ret; split; auto.
      }
    - cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF);

        try (cbn;
         try apply orutt_bind with (RR:=eq);
         [ apply orutt_trigger; cbn; eauto;
           [ intros [] [] _; auto
           | intros o CONTRA; inv CONTRA
           ]
         |
         ];
         intros [] [] _;
             apply orutt_Ret; split; auto).

      { cbn.
        apply orutt_bind with (RR:=dvalue_refine_strict).
        apply orutt_trigger; cbn; eauto.
        intros t1 t2 H; tauto.
        intros o CONTRA; inv CONTRA.
        intros r1 r2 H.
        apply orutt_Ret; tauto.
      }
      { cbn.
        apply orutt_bind with (RR:=uvalue_refine_strict).
        apply orutt_trigger; cbn; eauto.
        intros t1 t2 H; tauto.
        intros o CONTRA; inv CONTRA.
        intros r1 r2 H.
        apply orutt_Ret; tauto.
      }
    - cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF).
      + (* PickUnique *)
        cbn.
        eapply orutt_bind with (RR:=fun x y => dvalue_refine_strict (proj1_sig x) (proj1_sig y)).
        apply orutt_trigger; cbn; eauto.
        intros [t1] [t2] H; tauto.
        intros o CONTRA; inv CONTRA.
        intros [r1] [r2] H.
        apply orutt_Ret; tauto.
      + (* PickNonPoison *)
        cbn.
        eapply orutt_bind with (RR:=fun x y => dvalue_refine_strict (proj1_sig x) (proj1_sig y)).
        apply orutt_trigger; cbn; eauto.
        intros [t1] [t2] H; tauto.
        intros o CONTRA; inv CONTRA.
        intros [r1] [r2] H.
        apply orutt_Ret; tauto.
      + (* Pick *)
        cbn.
        eapply orutt_bind with (RR:=fun x y => dvalue_refine_strict (proj1_sig x) (proj1_sig y)).
        apply orutt_trigger; cbn; eauto.
        intros [t1] [t2] H; tauto.
        intros o CONTRA; inv CONTRA.
        intros [r1] [r2] H.
        apply orutt_Ret; tauto.
    - cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF).

      cbn.
      do 2 rewrite bind_trigger.
      change (inr1 (inr1 (inr1 (inl1 o0)))) with
        (@subevent _ _ (ReSum_inr IFun sum1 OOME
                          (IS2.LP.Events.MemoryE +' IS2.LP.Events.PickUvalueE +' OOME +' UBE +' DebugE +' FailureE)
                          (IS2.LP.Events.LLVMEnvE +' IS2.LP.Events.LLVMStackE)

           ) B o0).
      pstep; red; cbn.
      rewrite subevent_subevent.
      eapply EqVisOOM.
    Qed.

    eapply orutt_interp_state; eauto.
    { intros A B e1 e2 s1 s2 H H0.
      apply orutt_interp_global_h; auto.
    }
    { intros A o s.
      cbn.
      setoid_rewrite bind_trigger.
      exists (resum IFun A o).
      exists (fun x : A => SemNotations.Ret1 s x).
      reflexivity.
    }
  Qed.

  Lemma orutt_interp_intrinsics_h :
    forall A B e1 e2,
      event_refine_strict A B e1 e2 ->
      orutt event_refine_strict event_res_refine_strict
        (fun (a : A) (b : B) => event_res_refine_strict A B e1 a e2 b)
        (IS1.LLVM.Intrinsics.interp_intrinsics_h e1) (interp_intrinsics_h e2)
        (OOM:=OOME).
  Proof.
    intros A B e1 e2 REF.
    destruct e1; repeat (destruct e); repeat (destruct s).
    try
      solve
        [
          cbn in REF;
          destruct e2; try inv REF;
          repeat (break_match_hyp; try inv REF);
          cbn in *;
          pstep; red; cbn;
          constructor; cbn; auto;
          [ intros ? ? ?;
              left;
            pstep; red; cbn;
            constructor; auto
          | intros o CONTRA; inv CONTRA
          ]
        ].

    all: try
           solve
           [ cbn in REF;
             destruct e2; try inv REF;
             repeat (break_match_hyp; try inv REF);
             cbn in *;
             (pstep; red; cbn;
              constructor; cbn; try tauto;
              [ intros ? ? ?; left; apply orutt_Ret; tauto
              | intros o CONTRA; inv CONTRA
             ])
           |
             cbn in REF;
             destruct e2; try inv REF;
             repeat (break_match_hyp; try inv REF);
             cbn in *;
             (pstep; red; cbn;
              constructor; cbn;
              [ first [red; red; auto | tauto]
              | intros ? ? ?; left; apply orutt_Ret; tauto
              | intros o CONTRA; inv CONTRA
             ])
           ].

    -
      cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF);
        cbn in *.
      destruct H0 as [FEQ REFARGS]; subst.
      repeat break_inner_match_goal;
        try solve_orutt_raise.

      Lemma llvm_fabs_f32_agrees_fail :
        forall args1 args2 s,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_fabs_f32 args1 = inl s ->
          IS2.LLVM.Intrinsics.llvm_fabs_f32 args2 = inl s.
      Proof.
        intros args1 args2 s ARGS EXEC.
        destruct ARGS; cbn in *; try congruence.
        destruct x;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        destruct ARGS; cbn in *;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].
      Qed.

      Lemma llvm_fabs_f32_agrees_success :
        forall args1 args2 d1,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_fabs_f32 args1 = inr d1 ->
          exists d2,
            IS2.LLVM.Intrinsics.llvm_fabs_f32 args2 = inr d2 /\
              dvalue_refine_strict d1 d2.
      Proof.
        intros args1 args2 s ARGS EXEC.
        destruct ARGS; cbn in *; try congruence.
        destruct x;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        destruct ARGS; cbn in *;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        inv EXEC.
        unfold_dvalue_refine_strict_in H.
        inv H.
        eexists.
        split; eauto.
        unfold_dvalue_refine_strict.
        reflexivity.
      Qed.

      Lemma llvm_fabs_f64_agrees_fail :
        forall args1 args2 s,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_fabs_f64 args1 = inl s ->
          IS2.LLVM.Intrinsics.llvm_fabs_f64 args2 = inl s.
      Proof.
        intros args1 args2 s ARGS EXEC.
        destruct ARGS; cbn in *; try congruence.
        destruct x;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        destruct ARGS; cbn in *;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].
      Qed.

      Lemma llvm_fabs_f64_agrees_success :
        forall args1 args2 d1,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_fabs_f64 args1 = inr d1 ->
          exists d2,
            IS2.LLVM.Intrinsics.llvm_fabs_f64 args2 = inr d2 /\
              dvalue_refine_strict d1 d2.
      Proof.
        intros args1 args2 s ARGS EXEC.
        destruct ARGS; cbn in *; try congruence.
        destruct x;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        destruct ARGS; cbn in *;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        inv EXEC.
        unfold_dvalue_refine_strict_in H.
        inv H.
        eexists.
        split; eauto.
        unfold_dvalue_refine_strict.
        reflexivity.
      Qed.

      Lemma llvm_maxnum_f32_agrees_fail :
        forall args1 args2 s,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_maxnum_f32 args1 = inl s ->
          IS2.LLVM.Intrinsics.llvm_maxnum_f32 args2 = inl s.
      Proof.
        intros args1 args2 s ARGS EXEC.
        destruct ARGS; cbn in *; try congruence.
        destruct x;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        destruct ARGS; cbn in *;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        unfold_dvalue_refine_strict_in H; inv H.

        destruct ARGS; cbn in *; destruct x0;
          try
            solve
            [ unfold_dvalue_refine_strict_in H0;
              cbn in *;
              try break_match_hyp_inv;
              try inv H0;
              try congruence
            ].
      Qed.

      Lemma llvm_maxnum_f32_agrees_success :
        forall args1 args2 d1,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_maxnum_f32 args1 = inr d1 ->
          exists d2,
            IS2.LLVM.Intrinsics.llvm_maxnum_f32 args2 = inr d2 /\
              dvalue_refine_strict d1 d2.
      Proof.
        intros args1 args2 s ARGS EXEC.
        destruct ARGS; cbn in *; try congruence.
        destruct x;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        destruct ARGS; cbn in *;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        unfold_dvalue_refine_strict_in H; inv H.

        destruct ARGS; cbn in *; destruct x0;
          try
            solve
            [ unfold_dvalue_refine_strict_in H0;
              cbn in *;
              try break_match_hyp_inv;
              try inv H0;
              try congruence
            ].

        inv EXEC.
        unfold_dvalue_refine_strict_in H0.
        inv H0.
        eexists.
        split; eauto.
        unfold_dvalue_refine_strict.
        reflexivity.
      Qed.

      Lemma llvm_maxnum_f64_agrees_fail :
        forall args1 args2 s,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_maxnum_f64 args1 = inl s ->
          IS2.LLVM.Intrinsics.llvm_maxnum_f64 args2 = inl s.
      Proof.
        intros args1 args2 s ARGS EXEC.
        destruct ARGS; cbn in *; try congruence.
        destruct x;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        destruct ARGS; cbn in *;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        unfold_dvalue_refine_strict_in H; inv H.

        destruct ARGS; cbn in *; destruct x0;
          try
            solve
            [ unfold_dvalue_refine_strict_in H0;
              cbn in *;
              try break_match_hyp_inv;
              try inv H0;
              try congruence
            ].
      Qed.

      Lemma llvm_maxnum_f64_agrees_success :
        forall args1 args2 d1,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_maxnum_f64 args1 = inr d1 ->
          exists d2,
            IS2.LLVM.Intrinsics.llvm_maxnum_f64 args2 = inr d2 /\
              dvalue_refine_strict d1 d2.
      Proof.
        intros args1 args2 s ARGS EXEC.
        destruct ARGS; cbn in *; try congruence.
        destruct x;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        destruct ARGS; cbn in *;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        unfold_dvalue_refine_strict_in H; inv H.

        destruct ARGS; cbn in *; destruct x0;
          try
            solve
            [ unfold_dvalue_refine_strict_in H0;
              cbn in *;
              try break_match_hyp_inv;
              try inv H0;
              try congruence
            ].

        inv EXEC.
        unfold_dvalue_refine_strict_in H0.
        inv H0.
        eexists.
        split; eauto.
        unfold_dvalue_refine_strict.
        reflexivity.
      Qed.

      Lemma llvm_minimum_f32_agrees_fail :
        forall args1 args2 s,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_minimum_f32 args1 = inl s ->
          IS2.LLVM.Intrinsics.llvm_minimum_f32 args2 = inl s.
      Proof.
        intros args1 args2 s ARGS EXEC.
        destruct ARGS; cbn in *; try congruence.
        destruct x;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        destruct ARGS; cbn in *;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        unfold_dvalue_refine_strict_in H; inv H.

        destruct ARGS; cbn in *; destruct x0;
          try
            solve
            [ unfold_dvalue_refine_strict_in H0;
              cbn in *;
              try break_match_hyp_inv;
              try inv H0;
              try congruence
            ].
      Qed.

      Lemma llvm_minimum_f32_agrees_success :
        forall args1 args2 d1,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_minimum_f32 args1 = inr d1 ->
          exists d2,
            IS2.LLVM.Intrinsics.llvm_minimum_f32 args2 = inr d2 /\
              dvalue_refine_strict d1 d2.
      Proof.
        intros args1 args2 s ARGS EXEC.
        destruct ARGS; cbn in *; try congruence.
        destruct x;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        destruct ARGS; cbn in *;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        unfold_dvalue_refine_strict_in H; inv H.

        destruct ARGS; cbn in *; destruct x0;
          try
            solve
            [ unfold_dvalue_refine_strict_in H0;
              cbn in *;
              try break_match_hyp_inv;
              try inv H0;
              try congruence
            ].

        inv EXEC.
        unfold_dvalue_refine_strict_in H0.
        inv H0.
        eexists.
        split; eauto.
        unfold_dvalue_refine_strict.
        reflexivity.
      Qed.

      Lemma llvm_minimum_f64_agrees_fail :
        forall args1 args2 s,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_minimum_f64 args1 = inl s ->
          IS2.LLVM.Intrinsics.llvm_minimum_f64 args2 = inl s.
      Proof.
        intros args1 args2 s ARGS EXEC.
        destruct ARGS; cbn in *; try congruence.
        destruct x;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        destruct ARGS; cbn in *;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        unfold_dvalue_refine_strict_in H; inv H.

        destruct ARGS; cbn in *; destruct x0;
          try
            solve
            [ unfold_dvalue_refine_strict_in H0;
              cbn in *;
              try break_match_hyp_inv;
              try inv H0;
              try congruence
            ].
      Qed.

      Lemma llvm_minimum_f64_agrees_success :
        forall args1 args2 d1,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_minimum_f64 args1 = inr d1 ->
          exists d2,
            IS2.LLVM.Intrinsics.llvm_minimum_f64 args2 = inr d2 /\
              dvalue_refine_strict d1 d2.
      Proof.
        intros args1 args2 s ARGS EXEC.
        destruct ARGS; cbn in *; try congruence.
        destruct x;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        destruct ARGS; cbn in *;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        unfold_dvalue_refine_strict_in H; inv H.

        destruct ARGS; cbn in *; destruct x0;
          try
            solve
            [ unfold_dvalue_refine_strict_in H0;
              cbn in *;
              try break_match_hyp_inv;
              try inv H0;
              try congruence
            ].

        inv EXEC.
        unfold_dvalue_refine_strict_in H0.
        inv H0.
        eexists.
        split; eauto.
        unfold_dvalue_refine_strict.
        reflexivity.
      Qed.

      Lemma llvm_ushl_sat_1_agrees_success :
        forall args1 args2 d1,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_ushl_sat_1 args1 = inr d1 ->
          exists d2,
            IS2.LLVM.Intrinsics.llvm_ushl_sat_1 args2 = inr d2 /\
              dvalue_refine_strict d1 d2.
      Proof.
        intros args1 args2 s ARGS EXEC.
        destruct ARGS; cbn in *; try congruence.
        destruct x;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        destruct y;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        destruct ARGS; cbn in *;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        dvalue_refine_strict_inv H; inv H; subst_existT.
        repeat break_match_hyp_inv; subst_existT; cbn; inv ARGS;
          unfold_dvalue_refine_strict; inv H0;
          eexists; split; eauto;
          try rewrite Heqb;
          try rewrite Heqb0;
          try solve_dvalue_refine_strict; auto.
      Qed.

      Lemma llvm_ushl_sat_8_agrees_success :
        forall args1 args2 d1,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_ushl_sat_8 args1 = inr d1 ->
          exists d2,
            IS2.LLVM.Intrinsics.llvm_ushl_sat_8 args2 = inr d2 /\
              dvalue_refine_strict d1 d2.
      Proof.
        intros args1 args2 s ARGS EXEC.
        destruct ARGS; cbn in *; try congruence.
        destruct x;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        destruct y;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        destruct ARGS; cbn in *;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              repeat break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        dvalue_refine_strict_inv H; inv H; subst_existT;
          repeat break_match_hyp_inv; subst_existT; cbn; inv ARGS;
          unfold_dvalue_refine_strict; inv H0;
          eexists; split; eauto;
          try rewrite Heqb;
          try rewrite Heqb0;
          try solve_dvalue_refine_strict; auto.
      Qed.

      Lemma llvm_ushl_sat_16_agrees_success :
        forall args1 args2 d1,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_ushl_sat_16 args1 = inr d1 ->
          exists d2,
            IS2.LLVM.Intrinsics.llvm_ushl_sat_16 args2 = inr d2 /\
              dvalue_refine_strict d1 d2.
      Proof.
        intros args1 args2 s ARGS EXEC.
        destruct ARGS; cbn in *; try congruence.
        destruct x;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        destruct y;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        destruct ARGS; cbn in *;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              repeat break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        dvalue_refine_strict_inv H; inv H; subst_existT;
          repeat break_match_hyp_inv; subst_existT; cbn; inv ARGS;
          unfold_dvalue_refine_strict; inv H0;
          eexists; split; eauto;
          try rewrite Heqb;
          try rewrite Heqb0;
          try solve_dvalue_refine_strict; auto.
      Qed.

      Lemma llvm_ushl_sat_32_agrees_success :
        forall args1 args2 d1,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_ushl_sat_32 args1 = inr d1 ->
          exists d2,
            IS2.LLVM.Intrinsics.llvm_ushl_sat_32 args2 = inr d2 /\
              dvalue_refine_strict d1 d2.
      Proof.
        intros args1 args2 s ARGS EXEC.
        destruct ARGS; cbn in *; try congruence.
        destruct x;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        destruct y;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        destruct ARGS; cbn in *;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              repeat break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        dvalue_refine_strict_inv H; inv H; subst_existT;
          repeat break_match_hyp_inv; subst_existT; cbn; inv ARGS;
          unfold_dvalue_refine_strict; inv H0;
          eexists; split; eauto;
          try rewrite Heqb;
          try rewrite Heqb0;
          try solve_dvalue_refine_strict; auto.
      Qed.

      Lemma llvm_ushl_sat_64_agrees_success :
        forall args1 args2 d1,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_ushl_sat_64 args1 = inr d1 ->
          exists d2,
            IS2.LLVM.Intrinsics.llvm_ushl_sat_64 args2 = inr d2 /\
              dvalue_refine_strict d1 d2.
      Proof.
        intros args1 args2 s ARGS EXEC.
        destruct ARGS; cbn in *; try congruence.
        destruct x;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        destruct y;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        destruct ARGS; cbn in *;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              repeat break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        dvalue_refine_strict_inv H; inv H; subst_existT;
          repeat break_match_hyp_inv; subst_existT; cbn; inv ARGS;
          unfold_dvalue_refine_strict; inv H0;
          eexists; split; eauto;
          try rewrite Heqb;
          try rewrite Heqb0;
          try solve_dvalue_refine_strict; auto.
      Qed.

      Lemma llvm_ushl_sat_1_agrees_fail :
        forall args1 args2 s,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_ushl_sat_1 args1 = inl s ->
          IS2.LLVM.Intrinsics.llvm_ushl_sat_1 args2 = inl s.
      Proof.
        intros args1 args2 s ARGS EXEC.
        destruct ARGS; cbn in *; try congruence.
        destruct x;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        destruct y;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        dvalue_refine_strict_inv H; inv H; subst_existT.
        repeat break_match_hyp_inv; subst_existT; cbn; inv ARGS; auto;
          unfold_dvalue_refine_strict; inv H1;
          repeat break_match_hyp_inv; auto.

        inv H3; auto.
      Qed.

      Lemma llvm_ushl_sat_8_agrees_fail :
        forall args1 args2 s,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_ushl_sat_8 args1 = inl s ->
          IS2.LLVM.Intrinsics.llvm_ushl_sat_8 args2 = inl s.
      Proof.
        intros args1 args2 s ARGS EXEC.
        destruct ARGS; cbn in *; try congruence.
        destruct x;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        destruct y;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        dvalue_refine_strict_inv H; inv H; subst_existT.
        repeat break_match_hyp_inv; subst_existT; cbn; inv ARGS; auto;
          unfold_dvalue_refine_strict; inv H1;
          repeat break_match_hyp_inv; auto.

        inv H3; auto.
      Qed.

      Lemma llvm_ushl_sat_16_agrees_fail :
        forall args1 args2 s,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_ushl_sat_16 args1 = inl s ->
          IS2.LLVM.Intrinsics.llvm_ushl_sat_16 args2 = inl s.
      Proof.
        intros args1 args2 s ARGS EXEC.
        destruct ARGS; cbn in *; try congruence.
        destruct x;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        destruct y;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        dvalue_refine_strict_inv H; inv H; subst_existT.
        repeat break_match_hyp_inv; subst_existT; cbn; inv ARGS; auto;
          unfold_dvalue_refine_strict; inv H1;
          repeat break_match_hyp_inv; auto.

        inv H3; auto.
      Qed.

      Lemma llvm_ushl_sat_32_agrees_fail :
        forall args1 args2 s,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_ushl_sat_32 args1 = inl s ->
          IS2.LLVM.Intrinsics.llvm_ushl_sat_32 args2 = inl s.
      Proof.
        intros args1 args2 s ARGS EXEC.
        destruct ARGS; cbn in *; try congruence.
        destruct x;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        destruct y;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        dvalue_refine_strict_inv H; inv H; subst_existT.
        repeat break_match_hyp_inv; subst_existT; cbn; inv ARGS; auto;
          unfold_dvalue_refine_strict; inv H1;
          repeat break_match_hyp_inv; auto.

        inv H3; auto.
      Qed.

      Lemma llvm_ushl_sat_64_agrees_fail :
        forall args1 args2 s,
          Forall2 dvalue_refine_strict args1 args2 ->
          IS1.LLVM.Intrinsics.llvm_ushl_sat_64 args1 = inl s ->
          IS2.LLVM.Intrinsics.llvm_ushl_sat_64 args2 = inl s.
      Proof.
        intros args1 args2 s ARGS EXEC.
        destruct ARGS; cbn in *; try congruence.
        destruct x;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        destruct y;
          try
            solve
            [ unfold_dvalue_refine_strict_in H;
              cbn in *;
              try break_match_hyp_inv;
              try inv H;
              try congruence
            ].

        dvalue_refine_strict_inv H; inv H; subst_existT.
        repeat break_match_hyp_inv; subst_existT; cbn; inv ARGS; auto;
          unfold_dvalue_refine_strict; inv H1;
          repeat break_match_hyp_inv; auto.

        inv H3; auto.
      Qed.

      all:
        try solve
          [ pose proof (llvm_fabs_f32_agrees_fail _ _ _ REFARGS Heqs) as CONTRA;
            rewrite Heqs0 in CONTRA; inv CONTRA
          |
            pose proof (llvm_fabs_f64_agrees_fail _ _ _ REFARGS Heqs) as CONTRA;
            rewrite Heqs0 in CONTRA; inv CONTRA
          |
            pose proof (llvm_maxnum_f32_agrees_fail _ _ _ REFARGS Heqs) as CONTRA;
            rewrite Heqs0 in CONTRA; inv CONTRA
          |
            pose proof (llvm_maxnum_f64_agrees_fail _ _ _ REFARGS Heqs) as CONTRA;
            rewrite Heqs0 in CONTRA; inv CONTRA
          |
            pose proof (llvm_minimum_f32_agrees_fail _ _ _ REFARGS Heqs) as CONTRA;
            rewrite Heqs0 in CONTRA; inv CONTRA
          |
            pose proof (llvm_minimum_f64_agrees_fail _ _ _ REFARGS Heqs) as CONTRA;
            rewrite Heqs0 in CONTRA; inv CONTRA
          |
            pose proof (llvm_ushl_sat_1_agrees_fail _ _ _ REFARGS Heqs) as CONTRA;
            rewrite Heqs0 in CONTRA; inv CONTRA
          |
            pose proof (llvm_ushl_sat_8_agrees_fail _ _ _ REFARGS Heqs) as CONTRA;
            rewrite Heqs0 in CONTRA; inv CONTRA
          |
            pose proof (llvm_ushl_sat_16_agrees_fail _ _ _ REFARGS Heqs) as CONTRA;
            rewrite Heqs0 in CONTRA; inv CONTRA
          |
            pose proof (llvm_ushl_sat_32_agrees_fail _ _ _ REFARGS Heqs) as CONTRA;
            rewrite Heqs0 in CONTRA; inv CONTRA
          |
            pose proof (llvm_ushl_sat_64_agrees_fail _ _ _ REFARGS Heqs) as CONTRA;
            rewrite Heqs0 in CONTRA; inv CONTRA
          ].

      all:
        try solve
          [ pose proof (llvm_fabs_f32_agrees_success _ _ _ REFARGS Heqs) as [d2 [CONTRA REF]];
            rewrite Heqs0 in CONTRA; inv CONTRA; eauto using orutt_Ret
          | pose proof (llvm_fabs_f64_agrees_success _ _ _ REFARGS Heqs) as [d2 [CONTRA REF]];
            rewrite Heqs0 in CONTRA; inv CONTRA; eauto using orutt_Ret
          | pose proof (llvm_maxnum_f32_agrees_success _ _ _ REFARGS Heqs) as [d2 [CONTRA REF]];
            rewrite Heqs0 in CONTRA; inv CONTRA; eauto using orutt_Ret
          | pose proof (llvm_maxnum_f64_agrees_success _ _ _ REFARGS Heqs) as [d2 [CONTRA REF]];
            rewrite Heqs0 in CONTRA; inv CONTRA; eauto using orutt_Ret
          | pose proof (llvm_minimum_f32_agrees_success _ _ _ REFARGS Heqs) as [d2 [CONTRA REF]];
            rewrite Heqs0 in CONTRA; inv CONTRA; eauto using orutt_Ret
          | pose proof (llvm_minimum_f64_agrees_success _ _ _ REFARGS Heqs) as [d2 [CONTRA REF]];
            rewrite Heqs0 in CONTRA; inv CONTRA; eauto using orutt_Ret
          | pose proof (llvm_ushl_sat_1_agrees_success _ _ _ REFARGS Heqs) as [d2 [CONTRA REF]];
            rewrite Heqs0 in CONTRA; inv CONTRA; eauto using orutt_Ret
          | pose proof (llvm_ushl_sat_8_agrees_success _ _ _ REFARGS Heqs) as [d2 [CONTRA REF]];
            rewrite Heqs0 in CONTRA; inv CONTRA; eauto using orutt_Ret
          | pose proof (llvm_ushl_sat_16_agrees_success _ _ _ REFARGS Heqs) as [d2 [CONTRA REF]];
            rewrite Heqs0 in CONTRA; inv CONTRA; eauto using orutt_Ret
          | pose proof (llvm_ushl_sat_32_agrees_success _ _ _ REFARGS Heqs) as [d2 [CONTRA REF]];
            rewrite Heqs0 in CONTRA; inv CONTRA; eauto using orutt_Ret
          | pose proof (llvm_ushl_sat_64_agrees_success _ _ _ REFARGS Heqs) as [d2 [CONTRA REF]];
            rewrite Heqs0 in CONTRA; inv CONTRA; eauto using orutt_Ret
          ].

      cbn.
      pstep; red; cbn.
      constructor; cbn; try tauto.

      intros a b H.
      left; apply orutt_Ret.
      tauto.

      intros o CONTRA; inv CONTRA.
    - cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF);
        cbn in *.
      pstep; red; cbn.
      change (inr1 (inr1 (inr1 (inr1 (inl1 o0))))) with
        (@subevent _ _ (ReSum_inr IFun sum1 OOME
                          ((LLVMEnvE +' LLVMStackE) +' MemoryE +' PickUvalueE +' OOME +' UBE +' DebugE +' FailureE)
                          LLVMGEnvE

           ) B o0).
      rewrite subevent_subevent.
      eapply EqVisOOM.
  Qed.

  Lemma E1E2_interp_intrinsics_orutt_strict :
    forall t1 t2,
      L0_E1E2_orutt_strict t1 t2 ->
      L0_E1E2_orutt_strict (IS1.LLVM.Intrinsics.interp_intrinsics t1) (IS2.LLVM.Intrinsics.interp_intrinsics t2).
  Proof.
    intros t1 t2 RL0.
    red. red in RL0.

    unfold IS1.LLVM.Intrinsics.interp_intrinsics.
    unfold interp_intrinsics.
    cbn.

    eapply orutt_interp; eauto.
    { intros A B e1 e2 H.
      apply orutt_interp_intrinsics_h; auto.
    }
    { intros A o.
      exists (resum IFun A o).
      exists ret.
      reflexivity.
    }
  Qed.

  Lemma model_E1E2_01_orutt_strict :
    forall t1 t2 g1 g2,
      L0_E1E2_orutt_strict t1 t2 ->
      global_refine_strict g1 g2 ->
      L1_E1E2_orutt_strict (interp_global (IS1.LLVM.Intrinsics.interp_intrinsics t1) g1) (interp_global (IS2.LLVM.Intrinsics.interp_intrinsics t2) g2).
  Proof.
    intros t1 t2 g1 g2 RL0 GENVS.
    red in RL0.
    apply E1E2_interp_global_orutt_strict; auto.
    apply E1E2_interp_intrinsics_orutt_strict; auto.
  Qed.

  Lemma orutt_interp_local_stack_h :
    forall A B e1 e2 ls1 ls2,
      L1_refine_strict A B e1 e2 ->
      local_stack_refine_strict ls1 ls2 ->
      orutt L2_refine_strict L2_res_refine_strict
        (fun '(s0, a) '(s3, b) =>
           L1_res_refine_strict A B e1 a e2 b /\ (local_refine_strict × stack_refine_strict) s0 s3)
        (interp_local_stack_h (handle_local (v:=IS1.LP.Events.DV.uvalue)) e1 ls1)
        (interp_local_stack_h (handle_local (v:=uvalue)) e2 ls2)
        (OOM:=OOME).
  Proof.
    intros A B e1 e2 ls1 ls2 REF LSR.
    destruct e1; repeat (destruct e); repeat (destruct s);
    try
      solve
        [ cbn in REF;
          destruct e2; try inv REF;
          repeat (break_match_hyp; try inv REF);
          cbn in *;
          repeat rewrite bind_trigger;
          pstep; red; cbn;
          constructor;
          [ cbn; tauto
          | intros a b H;
            left; apply orutt_Ret;
            split; try tauto;
            destruct ls1, ls2; constructor; cbn in *; tauto
          | intros o CONTRA; inv CONTRA
          ]
        ].

    - cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF);
        cbn.
      eapply orutt_bind.
      apply orutt_trigger; cbn; eauto.
      intros [] [] ?; reflexivity.
      intros o CONTRA. inv CONTRA.
      intros [] [] ?.
      apply orutt_Ret; split; eauto.
      unfold local_stack_refine_strict in LSR.
      destruct ls1, ls2, LSR.
      constructor; cbn; eauto.
    - cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF);
        cbn.
      eapply orutt_bind.
      apply orutt_trigger; cbn; eauto.
      intros [] [] ?; reflexivity.
      intros o CONTRA. inv CONTRA.
      intros [] [] ?.
      apply orutt_Ret; split; eauto.
      unfold local_stack_refine_strict in LSR.
      destruct ls1, ls2, LSR.
      constructor; cbn; eauto.
    - cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF).
      + cbn in *.
        destruct ls1, ls2.
        cbn.
        repeat rewrite map_ret.
        apply orutt_Ret;
          split; try tauto.
        constructor; cbn in *; try tauto.
        apply local_stack_refine_strict_add; tauto.
      + cbn in *.
        destruct ls1, ls2.
        cbn.
        repeat rewrite map_ret.
        destruct LSR.
        pose proof H as FIND.
        do 2 red in FIND.
        specialize (FIND id0).
        red in FIND.
        break_match_hyp; break_match_hyp; inv FIND.
        repeat rewrite map_ret.
        apply orutt_Ret; split; try tauto.
        constructor; cbn in *; try tauto.

        apply orutt_bind with (RR:=local_refine_strict × uvalue_refine_strict).
        solve_orutt_raise.
        intros [l1 r1] [l2 r2] [L R]; cbn in *.
        apply orutt_Ret.
        split; try tauto.
        constructor; tauto.

    - cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF).
      + red in REF.
        cbn in *.
        destruct ls1, ls2.
        cbn.
        apply orutt_Ret;
          split; try tauto.
        constructor; cbn in *; try tauto.
        { (* TODO: Move this *)
          (* TODO: look at frame stack equivalence *)
          Lemma alist_refine_strict_fold_right_add_self :
            forall {K V}
              `{RD_K : @RelDec.RelDec K (@eq K)}
              `{RD_K_CORRECT : @RelDec.RelDec_Correct _ eq RD_K}
              (vs : FMapAList.alist K V),
              alist_refine eq vs (fold_right (fun '(id, v) => FMapAList.alist_add id v) [] vs).
          Proof.
            induction vs.
            - cbn; red; cbn.
              auto.
            - cbn; red; cbn.
              red in IHvs.
              intros k.
              unfold OptionUtil.option_rel2 in *.
              destruct a.
              break_inner_match_goal.
              + assert (k = k0).
                apply RelDec.rel_dec_correct; eauto.

                subst.
                rewrite alist_find_add_eq; auto.
              + rewrite alist_find_neq; eauto.
                apply IHvs.
                intros CONTRA.
                subst.
                rewrite Util.eq_dec_eq in Heqb.
                discriminate.
          Qed.

          Lemma alist_refine_strict_fold_right_add :
            forall {K V1 V2}
              `{RD_K : @RelDec.RelDec K (@eq K)}
              `{RD_K_CORRECT : @RelDec.RelDec_Correct _ eq RD_K}
              (R: V1 -> V2 -> Prop) vs1 vs2,
              alist_refine R vs1 vs2 ->
              alist_refine R (fold_right (fun '(id, v) => FMapAList.alist_add id v) [] vs1) (fold_right (fun '(id, v) => FMapAList.alist_add id v) [] vs2).
          Proof.
            intros K V1 V2 RD_K RD_K_CORRECT R vs1 vs2 REF.
            pose proof alist_refine_strict_fold_right_add_self vs1.
            red.
            red in H.
            unfold OptionUtil.option_rel2 in *.
            intros k.
            specialize (H k).
            break_match_hyp; try contradiction.
            - break_match_hyp; try contradiction; subst.
              pose proof alist_refine_strict_fold_right_add_self vs2.
              red in H.
              unfold OptionUtil.option_rel2 in *.
              specialize (H k).
              specialize (REF k).
              unfold OptionUtil.option_rel2 in *.
              rewrite Heqo in REF; auto.
              break_match_hyp; try contradiction.
              break_match_hyp; subst; auto.
            - specialize (REF k).
              unfold OptionUtil.option_rel2 in *.
              rewrite Heqo in REF; auto.
              break_match_hyp; try contradiction; subst.
              pose proof alist_refine_strict_fold_right_add_self vs2.
              red in H0.
              unfold OptionUtil.option_rel2 in *.
              specialize (H0 k).
              break_match_hyp; try contradiction; auto.
          Qed.

          apply alist_refine_strict_fold_right_add; auto.
        }

        apply stack_refine_strict_add; tauto.
      + cbn in *.
        destruct ls1, ls2.
        cbn.
        repeat rewrite map_ret.

        destruct LSR.
        destruct s; inv H0.
        -- solve_orutt_raise.
        -- apply orutt_Ret. split; auto.
    - (* Memory Events *)
      cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF);
        try solve [cbn;
         repeat rewrite bind_trigger;
         red; pstep; red; cbn;
         constructor; cbn; auto;
         [ intros ?a ?b ?H;
           left;
           pstep; red; cbn;
           constructor; cbn; auto;
           split; auto;
           destruct ls1, ls2; cbn in *;
           constructor; tauto
         | intros o CONTRA; inv CONTRA
          ]].
    - (* Pick events *)
      cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF);
        try solve [cbn;
         repeat rewrite bind_trigger;
         red; pstep; red; cbn;
         constructor; cbn; auto;
         [ intros ?a ?b ?H;
           left;
           pstep; red; cbn;
           constructor; cbn; auto;
           split; auto;
           destruct ls1, ls2; cbn in *;
           constructor; tauto
         | intros o CONTRA; inv CONTRA
          ]].
    - (* OOM Events *)
      cbn in REF;
        destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF).

      cbn.
      repeat rewrite bind_trigger.
      change (inr1 (inr1 (inl1 o0))) with
        (@subevent _ _ (ReSum_inr IFun sum1 OOME
                          (PickUvalueE +' OOME +' UBE +' DebugE +' FailureE)
                          MemoryE
           ) B o0).
      pstep; red; cbn.
      rewrite subevent_subevent.
      eapply EqVisOOM.
    - cbn in REF;
       destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF).
      cbn.
      repeat rewrite bind_trigger.
      pfold. red.
      cbn.
      constructor; cbn; auto.
      intros [] [] _.
      left.
      pstep; red; cbn.
      constructor.
      split; auto.
      red in LSR.
      destruct ls1, ls2.
      constructor; tauto.
      intros o CONTRA.
      inv CONTRA.
    - cbn in REF;
       destruct e2; try inv REF;
        repeat (break_match_hyp; try inv REF).
      cbn.
      repeat rewrite bind_trigger.
      pfold. red.
      cbn.
      constructor; cbn; auto.
      intros [].
      intros o CONTRA.
      inv CONTRA.
  Qed.

  Lemma model_E1E2_12_orutt_strict :
    forall t1 t2 ls1 ls2,
      L1_E1E2_orutt_strict t1 t2 ->
      local_stack_refine_strict ls1 ls2 ->
      L2_E1E2_orutt_strict (interp_local_stack t1 ls1) (interp_local_stack t2 ls2).
  Proof.
    intros t1 t2 ls1 ls2 RL1 LSR.
    red in RL1.

    unfold interp_local_stack.
    eapply orutt_interp_state; eauto.
    { unfold local_stack_refine_strict in *.
      destruct ls1, ls2;
      constructor; tauto.
    }

    intros A B e1 e2 s1 s2 H H0.
    eapply orutt_interp_local_stack_h; eauto.
    inv H0.
    destruct s1, s2; cbn in *; auto.

    intros A o s.
    exists o.
    cbn.
    setoid_rewrite bind_trigger.
    exists (fun x : A => SemNotations.Ret1 s x).
    reflexivity.
  Qed.

  Lemma model_E1E2_L1_orutt_strict_sound
    (p : list
           (LLVMAst.toplevel_entity
              LLVMAst.typ
              (LLVMAst.block LLVMAst.typ * list (LLVMAst.block LLVMAst.typ)))) :
    model_E1E2_L1_orutt_strict p p.
  Proof.
    apply model_E1E2_01_orutt_strict;
      [ apply model_E1E2_L0_orutt_strict_sound
      | apply global_refine_strict_empty
      ].
  Qed.

  Lemma model_E1E2_L2_orutt_strict_sound
    (p : list
           (LLVMAst.toplevel_entity
              LLVMAst.typ
              (LLVMAst.block LLVMAst.typ * list (LLVMAst.block LLVMAst.typ)))) :
    model_E1E2_L2_orutt_strict p p.
  Proof.
    apply model_E1E2_12_orutt_strict;
      [ apply model_E1E2_L1_orutt_strict_sound
      | apply local_stack_refine_strict_empty
      ].
  Qed.

End LangRefine.

Module MakeLangRefine
  (IS1 : InterpreterStack) (IS2 : InterpreterStack) (AC1 : AddrConvert IS1.LP.ADDR IS1.LP.PTOI IS2.LP.ADDR IS2.LP.PTOI) (AC2 : AddrConvert IS2.LP.ADDR IS2.LP.PTOI IS1.LP.ADDR IS1.LP.PTOI) (LLVM1 : LLVMTopLevel IS1) (LLVM2 : LLVMTopLevel IS2) (TLR1 : TopLevelRefinements IS1 LLVM1) (TLR2 : TopLevelRefinements IS2 LLVM2) (IPS : IPConvertSafe IS2.LP.IP IS1.LP.IP) (ACS : AddrConvertSafe IS2.LP.ADDR IS2.LP.PTOI IS1.LP.ADDR IS1.LP.PTOI AC2 AC1) (DVC : DVConvert IS1.LP IS2.LP AC1 IS1.LP.Events IS2.LP.Events) (DVCrev : DVConvert IS2.LP IS1.LP AC2 IS2.LP.Events IS1.LP.Events) (EC : EventConvert IS1.LP IS2.LP AC1 AC2 IS1.LP.Events IS2.LP.Events DVC DVCrev) (TC : TreeConvert IS1 IS2 AC1 AC2 DVC DVCrev EC) (VMEM_IP_PROP1 : VMemInt_Intptr_Properties IS1.LP.IP) (VMEM_IP_PROP2 : VMemInt_Intptr_Properties IS2.LP.IP) (VMEM_REF : VMemInt_Refine IS1.LP.IP IS2.LP.IP) (SIZEOF_REF : Sizeof_Refine IS1.LP.SIZEOF IS2.LP.SIZEOF) (ITOP_REF : ItoP_Refine IS1 IS2 AC1 AC2) : LangRefine IS1 IS2 AC1 AC2 LLVM1 LLVM2 TLR1 TLR2 IPS ACS DVC DVCrev EC TC VMEM_IP_PROP1 VMEM_IP_PROP2 VMEM_REF SIZEOF_REF ITOP_REF.
  Include LangRefine IS1 IS2 AC1 AC2 LLVM1 LLVM2 TLR1 TLR2 IPS ACS DVC DVCrev EC TC VMEM_IP_PROP1 VMEM_IP_PROP2 VMEM_REF SIZEOF_REF ITOP_REF.
End MakeLangRefine.

Module InfFinLangRefine := MakeLangRefine InterpreterStackBigIntptr InterpreterStack64BitIntptr InfToFinAddrConvert FinToInfAddrConvert TopLevelBigIntptr TopLevel64BitIntptr TopLevelRefinementsBigIntptr TopLevelRefinements64BitIntptr FinToInfIntptrConvertSafe FinToInfAddrConvertSafe DVCInfFin DVCFinInf ECInfFin TCInfFin VMemInt_Intptr_Properties_Inf VMemInt_Intptr_Properties_Fin VMemInt_Refine_InfFin Sizeof_Refine_InfFin ItoP_Refine_InfFin.

(* Just planning on using this for L4_convert from finite to infinite events. *)
(* Module FinInfLangRefine := MakeLangRefine InterpreterStack64BitIntptr InterpreterStackBigIntptr FinToInfAddrConvert InfToFinAddrConvert TopLevel64BitIntptr TopLevelBigIntptr TopLevelRefinementsBigIntptr FinToInfIntptrConvertSafe. DVCFinInf DVCInfFin ECFinInf . *)
