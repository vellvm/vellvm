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
     Semantics.LLVMParams
     Semantics.InfiniteToFinite.Conversions.BaseConversions
     Semantics.InfiniteToFinite.Conversions.DvalueConversions
     Semantics.InfiniteToFinite.Conversions.EventConversions
     Semantics.InfiniteToFinite.Conversions.TreeConversions
     Semantics.InfiniteToFinite.R2Injective
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
  intuition. inversion H1.
  intro C. intuition. inversion H2.
Defined.
Next Obligation.
  split. intros; intro C.
  intuition. inversion H2.
  intro C. intuition. inversion H1.
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
          IP_FIN.to_Z r_fin = IP_INF.to_Z r_inf.

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

  Parameter mshr_refine :
    forall x_fin y_fin r_fin x_inf y_inf,
      IP_FIN.to_Z x_fin = IP_INF.to_Z x_inf ->
      IP_FIN.to_Z y_fin = IP_INF.to_Z y_inf ->
      @mshr _ IP_FIN.VMemInt_intptr x_fin y_fin = r_fin ->
      exists r_inf,
        @mshr _ IP_INF.VMemInt_intptr x_inf y_inf = r_inf /\
          IP_FIN.to_Z r_fin = IP_INF.to_Z r_inf.

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
    rewrite Int64.add_signed.
    rewrite X, Y.
    rewrite Int64.signed_repr; eauto.

    (* TODO: Separate this into lemma? *)
    unfold Int64.add_overflow in Heqb.
    cbn in Heqb.
    break_match_hyp; cbn in Heqb; try discriminate.

    unfold Coqlib.zle in Heqb0.
    apply Bool.andb_true_iff in Heqb0.
    destruct Heqb0.

    apply Coqlib.proj_sumbool_true in H, H0.
    cbn in *.
    rewrite X, Y, Int64.signed_zero in *.
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

    unfold InterpreterStack64BitIntptr.LP.IP.to_Z, InterpreterStackBigIntptr.LP.IP.to_Z in *.
    rewrite Int64.sub_signed.
    rewrite X, Y.
    rewrite Int64.signed_repr; eauto.

    (* TODO: Separate this into lemma? *)
    unfold Int64.sub_overflow in Heqb.
    cbn in Heqb.
    break_match_hyp; cbn in Heqb; try discriminate.

    unfold Coqlib.zle in Heqb0.
    apply Bool.andb_true_iff in Heqb0.
    destruct Heqb0.

    apply Coqlib.proj_sumbool_true in H, H0.
    cbn in *.
    rewrite X, Y, Int64.signed_zero in *.
    lia.
  Qed.

  Lemma mmul_refine :
    forall x_fin y_fin r_fin x_inf y_inf,
      InterpreterStack64BitIntptr.LP.IP.to_Z x_fin = InterpreterStackBigIntptr.LP.IP.to_Z x_inf ->
      InterpreterStack64BitIntptr.LP.IP.to_Z y_fin = InterpreterStackBigIntptr.LP.IP.to_Z y_inf ->
      @mmul _ InterpreterStack64BitIntptr.LP.IP.VMemInt_intptr x_fin y_fin = NoOom r_fin ->
      exists r_inf,
        @mmul _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr x_inf y_inf = NoOom r_inf /\
          InterpreterStack64BitIntptr.LP.IP.to_Z r_fin = InterpreterStackBigIntptr.LP.IP.to_Z r_inf.
  Proof.
    intros x_fin y_fin r_fin x_inf y_inf X Y MUL.
    cbn.
    exists (x_inf * y_inf)%Z.
    split; auto.

    cbn in MUL.
    break_match_hyp_inv.

    unfold InterpreterStack64BitIntptr.LP.IP.to_Z, InterpreterStackBigIntptr.LP.IP.to_Z in *.
    rewrite Int64.mul_signed.
    rewrite X, Y.
    rewrite Int64.signed_repr; eauto.
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
    split; auto.

  (*   Opaque Z.sub. *)
  (*   cbn in SHL. *)

  (*   break_match_hyp_inv. *)
  (*   break_match_hyp_inv. *)

  (*   unfold Int64.shl in *. *)
  (*   unfold InterpreterStack64BitIntptr.LP.IP.to_Z, InterpreterStackBigIntptr.LP.IP.to_Z in *. *)
  (*   unfold Int64.signed in X, Y. *)
  (*   break_match_hyp; break_match_hyp. *)
  (*   - rewrite X, Y. *)
  (*     rewrite Int64.signed_repr; eauto. *)

  (*   mshl := *)
  (*     fun x y => *)
  (*       let res := Int64.shl x y in *)
  (*       if Int64.signed res =? Int64.min_signed *)
  (*       then Oom "IP64Bit left shift overflow (res is min signed, should not happen)." *)
  (*       else *)
  (*         let nres := Int64.negative res in *)
  (*         if (negb (Z.shiftr (Int64.unsigned x) *)
  (*                     (64%Z - Int64.unsigned y) *)
  (*                   =? (Int64.unsigned nres) *)
  (*                      * (Z.pow 2 (Int64.unsigned y) - 1))%Z) *)
  (*         then Oom "IP64Bit left shift overflow." *)
  (*         else ret res; *)
    (* Qed. *)
  Admitted.

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
  Admitted.

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
    cbn.
    exists (x_inf / y_inf)%Z.
    split; auto.

    cbn in *.
    break_match_hyp_inv.

    unfold InterpreterStack64BitIntptr.LP.IP.to_Z, InterpreterStackBigIntptr.LP.IP.to_Z in *.
    unfold Int64.divs.
    rewrite X, Y.
    rewrite Int64.signed_repr; eauto.
  Admitted.

  Lemma mshr_refine :
    forall x_fin y_fin r_fin x_inf y_inf,
      InterpreterStack64BitIntptr.LP.IP.to_Z x_fin = InterpreterStackBigIntptr.LP.IP.to_Z x_inf ->
      InterpreterStack64BitIntptr.LP.IP.to_Z y_fin = InterpreterStackBigIntptr.LP.IP.to_Z y_inf ->
      @mshr _ InterpreterStack64BitIntptr.LP.IP.VMemInt_intptr x_fin y_fin = r_fin ->
      exists r_inf,
        @mshr _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr x_inf y_inf = r_inf /\
          InterpreterStack64BitIntptr.LP.IP.to_Z r_fin = InterpreterStackBigIntptr.LP.IP.to_Z r_inf.
  Proof.
    intros x_fin y_fin r_fin x_inf y_inf X Y SHR.
    cbn.
    exists (Z.shiftr x_inf y_inf).
    split; auto.

    cbn in SHR.
    subst.

    unfold InterpreterStack64BitIntptr.LP.IP.to_Z, InterpreterStackBigIntptr.LP.IP.to_Z in *.
  Admitted.

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
  Admitted.

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
    cbn.
    exists (x_inf mod y_inf)%Z.
    split; auto.

    cbn in MOD.
    subst.

    unfold InterpreterStack64BitIntptr.LP.IP.to_Z, InterpreterStackBigIntptr.LP.IP.to_Z in *.
    break_match_hyp_inv.
  Admitted.

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
  Admitted.

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
    unfold Int64.and in AND.
    subst.

    unfold InterpreterStack64BitIntptr.LP.IP.to_Z, InterpreterStackBigIntptr.LP.IP.to_Z in *.
    unfold Int64.signed in X, Y.
    break_match_hyp; break_match_hyp.
    - rewrite X, Y.
      rewrite Int64.signed_repr; eauto.
  Admitted.

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
    unfold Int64.or in OR.
    subst.

    unfold InterpreterStack64BitIntptr.LP.IP.to_Z, InterpreterStackBigIntptr.LP.IP.to_Z in *.
  Admitted.

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
    unfold Int64.xor in XOR.
    subst.

    unfold InterpreterStack64BitIntptr.LP.IP.to_Z, InterpreterStackBigIntptr.LP.IP.to_Z in *.
  Admitted.

End VMemInt_Refine_InfFin.

Module Type LangRefine (IS1 : InterpreterStack) (IS2 : InterpreterStack) (AC1 : AddrConvert IS1.LP.ADDR IS1.LP.PTOI IS2.LP.ADDR IS2.LP.PTOI) (AC2 : AddrConvert IS2.LP.ADDR IS2.LP.PTOI IS1.LP.ADDR IS1.LP.PTOI) (LLVM1 : LLVMTopLevel IS1) (LLVM2 : LLVMTopLevel IS2) (TLR : TopLevelRefinements IS2 LLVM2) (IPS : IPConvertSafe IS2.LP.IP IS1.LP.IP) (ACS : AddrConvertSafe IS2.LP.ADDR IS2.LP.PTOI IS1.LP.ADDR IS1.LP.PTOI AC2 AC1) (DVC : DVConvert IS1.LP IS2.LP AC1 IS1.LP.Events IS2.LP.Events) (DVCrev : DVConvert IS2.LP IS1.LP AC2 IS2.LP.Events IS1.LP.Events) (EC : EventConvert IS1.LP IS2.LP AC1 AC2 IS1.LP.Events IS2.LP.Events DVC DVCrev) (TC : TreeConvert IS1 IS2 AC1 AC2 DVC DVCrev EC) (VMEM_IP_PROP1 : VMemInt_Intptr_Properties IS1.LP.IP) (VMEM_IP_PROP2 : VMemInt_Intptr_Properties IS2.LP.IP) (VMEM_REF : VMemInt_Refine IS1.LP.IP IS2.LP.IP).
  Import TLR.

  Import TC.
  Import EC.
  Import DVC.
  Import IPS.
  Import ACS.

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
  (* Lemma Returns_uvalue_convert_L1_L2 : *)
  (*   forall a d f u l t args, *)
  (*     EC.DVCrev.dvalue_convert a = NoOom d -> *)
  (*     EC.DVC.uvalue_convert f = NoOom u -> *)
  (*     @Returns (E2.ExternalCallE +' OOME +' UBE +' DebugE +' FailureE) E2.DV.dvalue a (trigger (E2.ExternalCall t u l)) -> *)
  (*     @Returns (E1.ExternalCallE +' OOME +' UBE +' DebugE +' FailureE) E1.DV.dvalue d (trigger (E1.ExternalCall t f args)). *)
  (* Proof. *)
  (* Admitted. *)

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

  (* Lemma Returns_uvalue_convert_strict_L0 : *)
  (*   forall a d f u l t args, *)
  (*     (* EC.DVCrev.dvalue_convert_strict a = NoOom d -> *) *)
  (*     (* EC.DVC.uvalue_convert_strict f = NoOom u -> *) *)
  (*     @Returns E2.L0 E2.DV.dvalue a (trigger (E2.ExternalCall t u l)) -> *)
  (*     @Returns E1.L0 E1.DV.dvalue d (trigger (E1.ExternalCall t f args)). *)
  (* Proof. *)
  (*   intros a d f u l t args (* DVCONV UVCONV *) RET. *)

  (*   eapply ReturnsVis. *)
  (*   unfold trigger. *)
  (*   reflexivity. *)
  (*   cbn. *)
  (*   constructor. *)
  (*   reflexivity. *)


  (*   remember (trigger (E2.ExternalCall t u l)) as call. *)
  (*   assert (call ≈ trigger (E2.ExternalCall t u l)) as CALL. *)
  (*   { subst; reflexivity. } *)
  (*   clear Heqcall. *)
  (*   induction RET; subst; auto. *)
  (*   - unfold trigger in CALL. *)
  (*     rewrite H in CALL. *)
  (*     pinversion CALL. *)
  (*   - forward IHRET. *)
  (*     { rewrite <- tau_eutt. *)
  (*       rewrite <- H. *)
  (*       auto. *)
  (*     } *)
  (*     auto. *)
  (*   - (* Must be a contradiction...? *) *)
  (*     eapply ReturnsVis. *)
  (*     unfold trigger. *)
  (*     reflexivity. *)
  (*     cbn. *)
  (*     constructor. *)
  (*     reflexivity. *)
  (* Qed. *)

  (* Lemma Returns_uvalue_convert_L3 : *)
  (*   forall a d f u l t args, *)
  (*     EC.DVCrev.dvalue_convert a = NoOom d -> *)
  (*     EC.DVC.uvalue_convert f = NoOom u -> *)
  (*     @Returns E2.L3 E2.DV.dvalue a (trigger (E2.ExternalCall t u l)) -> *)
  (*     @Returns E1.L3 E1.DV.dvalue d (trigger (E1.ExternalCall t f args)). *)
  (* Proof. *)
  (* Admitted. *)

  Lemma refine_OOM_h_L0_convert_tree_strict :
    forall {T} x_inf y_inf (RR : relation T),
      refine_OOM_h RR x_inf y_inf ->
      refine_OOM_h RR (L0_convert_tree_strict x_inf) (L0_convert_tree_strict y_inf).
  Proof.
    intros T.

    unfold refine_OOM_h, L0_convert_tree_strict, refine_OOM_h_flip.
    intros.
    eapply interp_prop_oom_l_eutt_Proper; try typeclasses eauto.
    rewrite (unfold_interp y_inf); reflexivity.
    rewrite (unfold_interp x_inf); reflexivity.
    cbn.

    match goal with
    | |- interp_prop_oom_l _ _ _ ?l ?r => remember l as i; remember r as i0
    end.

    assert (i ≅ _interp EC.L0_convert_strict (observe y_inf)). {
      rewrite Heqi. reflexivity.
    } clear Heqi.
    remember (_interp EC.L0_convert_strict (observe x_inf)).
    assert (i0 ≅ _interp EC.L0_convert_strict (observe x_inf)). {
      subst; reflexivity.
    } clear Heqi1 Heqi0.
    revert x_inf y_inf H i i0 H0 H1.

    pcofix CIH.

    intros * H.
    punfold H; red in H.
    remember (observe y_inf) as oy; remember (observe x_inf) as ox.
    clear Heqoy Heqox.

    induction H; pclearbot; intros; subst; auto.
    - pstep. cbn in H1, H2.
      rewrite itree_eta in H1, H2.
      red.
      destruct (observe i) eqn: Heqi; destruct (observe i0) eqn: Heqi0;
        try apply eqit_inv in H1; try apply eqit_inv in H2; cbn in H1, H2; try contradiction; auto.
      subst; constructor; auto.
    - pstep. cbn in H1, H2.
      rewrite itree_eta in H1, H2.
      red.
      destruct (observe i) eqn: Heqi; destruct (observe i0) eqn: Heqi0;
        try apply eqit_inv in H1; try apply eqit_inv in H2; cbn in H1, H2; try contradiction; auto.
      subst; constructor; auto.

      right; eapply CIH; eauto;
      rewrite unfold_interp in H1, H2; auto.
    - pstep. cbn in H1, H2.
      rewrite itree_eta in H1, H2.
      red.
      destruct (observe i) eqn: Heqi;
        try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
      subst; constructor; auto.
      rewrite unfold_interp in H1.
      specialize (IHinterp_prop_oomTF _ _ H1 H2).
      punfold IHinterp_prop_oomTF.
    - pstep. cbn in H1, H2.
      rewrite itree_eta in H1, H2.
      red.
      destruct (observe i0) eqn: Heqi;
        try apply eqit_inv in H2; cbn in H2; try contradiction; auto.
      subst; constructor; auto.
      rewrite unfold_interp in H2.
      specialize (IHinterp_prop_oomTF _ _ H1 H2).
      punfold IHinterp_prop_oomTF.
    - pstep. apply bisimulation_is_eq in HT1.
      rewrite HT1 in H1. cbn in H1.
      destruct (resum IFun A e).
      cbn in H1.
      repeat setoid_rewrite bind_vis in H1.
      apply bisimulation_is_eq in H1. rewrite H1.
      econstructor; eauto.
      eapply eqit_Vis; intros; inv u.
      destruct u0.
    - discriminate.
    - pstep. cbn in HSPEC, KS. red in KS, HSPEC.
      rewrite HSPEC in KS.

      rewrite itree_eta in H1, H2.
      repeat destruct e; cbn in *.
      + rewrite bind_bind in H1.
        unfold lift_OOM in H1.
        rewrite bind_trigger in KS.
        cbn in *.
        destruct (DVC.uvalue_convert_strict f) eqn : Hf.
        { rewrite bind_ret_l, bind_bind in H1.
          destruct
            (map_monad_In args
              (fun (elt : E1.DV.dvalue) (_ : In elt args) => DVC.dvalue_convert_strict elt)) eqn: Hm.
          { rewrite bind_ret_l, bind_bind in H1.
            rewrite bind_trigger in H1.

            destruct (observe i) eqn: Heqi;
              try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
            red.
            setoid_rewrite Heqi.
            destruct H1 as (?&?&?).
            dependent destruction x.
            red in H, H0.
            econstructor; [ constructor | ..]; eauto; cycle 1.
            - red; reflexivity.
            - cbn in *.
              rewrite <- unfold_interp in H2.
              rewrite <- itree_eta in H2.
              red.
              rewrite H2. rewrite KS. rewrite interp_vis. cbn.
              rewrite bind_bind. unfold lift_OOM.
              rewrite Hf. setoid_rewrite bind_ret_l.
              setoid_rewrite bind_bind. rewrite Hm.
              setoid_rewrite bind_ret_l.
              setoid_rewrite bind_bind.
              setoid_rewrite bind_trigger.
              unfold subevent.
              subst.
              eapply eqit_Vis.
              intros u0.
              Unshelve.
              2: intros [].
              2: exact (fun u0 : E2.DV.dvalue =>
              ITree.bind match DVCrev.dvalue_convert_strict u0 with
                        | NoOom a0 => ret a0
                        | Oom s => raise_oom s
                         end (fun x1 : E1.DV.dvalue => Tau (interp EC.L0_convert_strict (k2 x1)))).
              reflexivity.
            - cbn. specialize (H0 a). subst.
              eapply bisimulation_is_eq in H0.
              rewrite H0.
              destruct (DVCrev.dvalue_convert_strict a) eqn: Ht.
              + setoid_rewrite HSPEC in HK. subst.
                (* TODO: Originally used Returns_uvalue_convert_L0
                applied to H3... But it seems Returns is weird with
                the vis case and allows any value to be
                returned...? *)
                rename H2 into H2'.
                pose proof Returns_ExternalCall_L0 d f t args as H3.
                specialize (HK _ H3). pclearbot.
                pose proof @bind_ret_l as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ.
                pose proof @bind_ret_l as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ.
                pstep; constructor; eauto. right; eauto.
                eapply CIH; try rewrite <- unfold_interp; try reflexivity.
                eapply HK.
              + setoid_rewrite HSPEC in HK. subst.
                unfold raiseOOM.
                pose proof @bind_bind as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ.
                pose proof @bind_trigger as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ.
                pose proof @bind_bind as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ.
                pose proof @bind_trigger as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ.
                pstep; econstructor; eauto. unfold subevent.
                reflexivity. }
          { unfold raiseOOM in H1. rewrite bind_trigger in H1.
            red. destruct (observe i) eqn: Heqi;
              try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
            destruct H1 as (?&?&?).
            dependent destruction x.
            cbn in *; subst.
            observe_vis; solve_interp_prop_oom.
        } }

          unfold raiseOOM in H1. rewrite bind_trigger in H1.
          red. destruct (observe i) eqn: Heqi;
            try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
          destruct H1 as (?&?&?).
          dependent destruction x.
          cbn in *; subst.
          observe_vis; solve_interp_prop_oom.
      + (* stdout *)
        red.
        setoid_rewrite bind_trigger in H1.
        rewrite <- (itree_eta_ i) in H1.
        rewrite <- (itree_eta_ i0) in H2.

        pinversion H1; subst_existT; try inv CHECK.
        eapply Interp_Prop_OomT_Vis
          with
          (ta:=(interp L0_convert_strict (trigger (inl1 (E1.IO_stdout str)))))
          (k2:=(fun r0 : unit => interp L0_convert_strict (k2 r0))).
        3: {
          red.
          setoid_rewrite H2.
          rewrite <- unfold_interp.
          setoid_rewrite KS.
          rewrite interp_bind.
          reflexivity.
        }

        2: {
          red.
          rewrite interp_trigger.
          cbn.
          reflexivity.
        }

        intros [] RET.
        specialize (REL tt).
        left.
        eapply paco2_mon_bot; eauto.
        rewrite REL.
        rewrite tau_eutt.

        specialize (HK tt).
        forward HK.
        rewrite HSPEC.
        eapply ReturnsVis.
        unfold trigger.
        reflexivity.
        cbn.
        constructor.
        reflexivity.

        pclearbot.

        (* TODO: Move this... Can this be generalized? *)
        Set Nested Proofs Allowed.
        Lemma interp_prop_oom'_refine_OOM_interp :
          forall {T} (RR : relation T) t1 t2,
            paco2
              (interp_prop_oomT_ (OOM:=OOME) (refine_OOM_handler (E:=E1.L0)) (flip RR) (@refine_OOM_k_spec E1.L0) true
                 true true false) bot2 t1 t2 ->
            paco2
              (interp_prop_oomT_ (OOM:=OOME) (refine_OOM_handler (E:=E2.L0)) (flip RR) (@refine_OOM_k_spec E2.L0) true true
                 true false) bot2 (interp L0_convert_strict t1) (interp L0_convert_strict t2).
        Proof.
          intros T RR.
          pcofix CIH.
          intros t1 t2 REL.

          rewrite (itree_eta_ t1) in *.
          rewrite (itree_eta_ t2) in *.
          genobs t1 ot1.
          genobs t2 ot2.
          clear t1 t2 Heqot1 Heqot2.

          punfold REL; red in REL; cbn in REL.
          induction REL.
          - eapply paco2_mon_bot; eauto.
            setoid_rewrite interp_ret.
            pstep; red; cbn.
            constructor; auto.
          - pstep; red; cbn.
            constructor.
            right.
            eapply CIH.
            pclearbot; eauto.
          - (* TauL *)
            pstep; red; cbn.
            constructor; auto.
            punfold IHREL; eauto.
          - (* TauR *)
            pstep; red; cbn.
            constructor; auto.
            punfold IHREL; eauto.
          - (* Vis_OOM_L *)
            pinversion HT1; subst_existT; try inv CHECK0.
            eapply paco2_mon_bot; eauto.
            setoid_rewrite interp_vis.
            destruct e.
            cbn.
            setoid_rewrite Raise.raiseOOM_bind_itree.
            pstep; red; cbn.
            observe_vis.
            eapply Interp_Prop_OomT_Vis_OOM_L; eauto.
            reflexivity.
          - (* Vis_OOM_R *)
            inv CHECK.
          - (* Vis vis *)
            red in HSPEC, KS.
            rewrite HSPEC in KS.

            eapply paco2_mon_bot; eauto.

            setoid_rewrite unfold_interp.
            cbn.
            unfold L0_convert_strict.
            destruct e.
            + destruct e.
            cbn.
            pstep; red; cbn.
        Abort.

        admit.
        (* apply interp_prop_oom'_refine_OOM_interp.
        eauto. *)
      + (* Stderr *)
        red.
        setoid_rewrite bind_trigger in H1.
        rewrite <- (itree_eta_ i) in H1.
        rewrite <- (itree_eta_ i0) in H2.

        pinversion H1; subst_existT; try inv CHECK.
        eapply Interp_Prop_OomT_Vis
          with
          (ta:=(interp L0_convert_strict (trigger (inl1 (E1.IO_stderr str)))))
          (k2:=(fun r0 : unit => interp L0_convert_strict (k2 r0))).
        3: {
          red.
          setoid_rewrite H2.
          rewrite <- unfold_interp.
          setoid_rewrite KS.
          rewrite interp_bind.
          reflexivity.
        }

        2: {
          red.
          rewrite interp_trigger.
          cbn.
          reflexivity.
        }

        intros [] RET.
        specialize (REL tt).
        left.
        eapply paco2_mon_bot; eauto.
        rewrite REL.
        rewrite tau_eutt.

        specialize (HK tt).
        forward HK.
        rewrite HSPEC.
        eapply ReturnsVis.
        unfold trigger.
        reflexivity.
        cbn.
        constructor.
        reflexivity.

        pclearbot.

        admit.
        (* apply interp_prop_oom'_refine_OOM_interp. *)
        (* eauto. *)
      + destruct s.
        { (* Intrinsic *)
          admit.
        }
        destruct s.
        { (* Globals *)
          admit.
        }
        destruct s.
        { (* Locals + Stack *)
          admit.
        }
        destruct s.
        { (* Memory *)
          (* TODO: separate out? *)
          destruct m.
          { (* MemPush *)
            cbn in *.
            red.
            rewrite <- itree_eta in H1.
            admit.
          }
          admit.
          admit.
          admit.
          admit.
        }
        destruct s.
        { (* Pick *)
          admit.
        }
        destruct s.
        * unfold raiseOOM in H1.
          destruct o.
          cbn in H1.
          rewrite bind_bind, bind_trigger in H1.
          rewrite itree_eta in H1, H2.
          red.
          destruct (observe i) eqn: Heqi;
            try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
          destruct H1 as (?&?&?).
          dependent destruction x.
          cbn in *; subst.
          observe_vis; solve_interp_prop_oom.
        * destruct s; try destruct u; cbn in H1.
          -- repeat red in HTA.
              unfold raiseUB in H1. rewrite bind_trigger in H1.
              red.
              destruct (observe i) eqn: Heqi;
                try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
              destruct H1 as (?&?&?).
              dependent destruction x.
              red in H, H0.
              eapply Interp_Prop_OomT_Vis; eauto.
              repeat red. intros.
              inv a.
              red; reflexivity.
              subst.
              setoid_rewrite <- itree_eta in H2.
              red. rewrite H2.
              rewrite <- unfold_interp.
              rewrite KS.              
              repeat setoid_rewrite bind_trigger.
              setoid_rewrite interp_vis.
              cbn.
              setoid_rewrite bind_trigger. rewrite bind_vis. cbn in *; subst. eapply eqit_Vis.
              intros [].
          -- destruct s; try destruct u; cbn in H1.
             ++ destruct d. cbn in H1.
                rewrite <- unfold_interp in H2.

                setoid_rewrite bind_trigger in H1.
                setoid_rewrite bind_trigger in KS.

                red.
                destruct (observe i) eqn: Heqi;
                  try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
                destruct H1 as (?&?&?).
                dependent destruction x.
                red in H, H0. subst.
                assert (Returns tt ta).
                { rewrite HSPEC. unfold trigger. eapply ReturnsVis; eauto.
                  unfold subevent. reflexivity.
                  constructor; reflexivity. }
                specialize (HK _ H). pclearbot.
                eapply Interp_Prop_OomT_Vis; eauto.
                ** intros. red in H0. specialize (H0 tt).
                   eapply bisimulation_is_eq in H0. destruct a.
                   rewrite H0.
                   right; eapply CIH.
                   2 : { rewrite <- interp_tau, <- unfold_interp. reflexivity. }
                   pstep; econstructor; eauto. punfold HK.
                   rewrite <- unfold_interp. Unshelve.
                   3: exact (fun x => interp EC.L0_convert_strict (k2 x)). reflexivity.
                   intros [].
                   all : shelve.
                ** red; reflexivity.
                ** rewrite <- itree_eta in H2.
                   red.
                   rewrite H2. rewrite KS.
                   rewrite interp_vis. cbn. unfold debug.
                   do 2 rewrite bind_trigger. unfold subevent, resum, ReSum_inr.
                   eapply eqit_Vis. intros. rewrite tau_eutt. reflexivity.
             ++ repeat red in HTA.
                destruct f. cbn in H1. setoid_rewrite bind_trigger in H1.
                red.
                destruct (observe i) eqn: Heqi;
                  try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
                destruct H1 as (?&?&?).
                dependent destruction x.
                red in H, H0. cbn in *; subst.
                eapply Interp_Prop_OomT_Vis; eauto.
                intros. inv a.
                red; reflexivity.
                red.
                setoid_rewrite <- itree_eta in H2. rewrite H2.
                rewrite <- unfold_interp.
                rewrite KS. cbn. rewrite interp_bind.
                rewrite interp_trigger. cbn. unfold LLVMEvents.raise.
                do 2 rewrite bind_trigger. rewrite bind_vis.
                apply eqit_Vis.
                intros [].
                Unshelve.
                all : eauto.
  Abort.

  Lemma refine_OOM_h_L1_convert_tree_strict :
    forall {T} x_inf y_inf (RR : relation T),
      refine_OOM_h RR x_inf y_inf ->
      refine_OOM_h RR (L1_convert_tree_strict x_inf) (L1_convert_tree_strict y_inf).
  Proof.
  Abort.

  Lemma refine_OOM_h_L2_convert_tree_strict :
    forall {T} x_inf y_inf (RR : relation T),
      refine_OOM_h RR x_inf y_inf ->
      refine_OOM_h RR (L2_convert_tree_strict x_inf) (L2_convert_tree_strict y_inf).
  Proof.
  Abort.

  Lemma refine_OOM_h_L3_convert_tree_strict :
    forall {T} x_inf y_inf (RR : relation T),
      refine_OOM_h RR x_inf y_inf ->
      refine_OOM_h RR (L3_convert_tree_strict x_inf) (L3_convert_tree_strict y_inf).
  Proof.
    (* intros T. *)

    (* unfold refine_OOM_h, L3_convert_tree, refine_OOM_h_flip. *)
    (* intros. *)
    (* rewrite (unfold_interp y_inf). *)
    (* rewrite (unfold_interp x_inf). *)
    (* cbn. *)

    (* match goal with *)
    (* | |- interp_prop _ _ ?l ?r => remember l as i; remember r as i0 *)
    (* end. *)

    (* assert (i ≅ _interp EC.L3_convert (observe y_inf)). { *)
    (*   rewrite Heqi. reflexivity. *)
    (* } clear Heqi. *)
    (* remember (_interp EC.L3_convert (observe x_inf)). *)
    (* assert (i0 ≅ _interp EC.L3_convert (observe x_inf)). { *)
    (*   subst; reflexivity. *)
    (* } clear Heqi1 Heqi0. *)
    (* revert x_inf y_inf H i i0 H0 H1. *)

    (* pcofix CIH. *)

    (* intros * H. *)
    (* punfold H; red in H. *)
    (* remember (observe y_inf) as oy; remember (observe x_inf) as ox. *)
    (* clear Heqoy Heqox. *)

    (* induction H; pclearbot; intros; subst; auto. *)
    (* - pstep. cbn in H1, H2. *)
    (*   rewrite itree_eta in H1, H2. *)
    (*   red. *)
    (*   destruct (observe i) eqn: Heqi; destruct (observe i0) eqn: Heqi0; *)
    (*     try apply eqit_inv in H1; try apply eqit_inv in H2; cbn in H1, H2; try contradiction; auto. *)
    (*   subst; constructor; auto. *)
    (* - pstep. cbn in H1, H2. *)
    (*   rewrite itree_eta in H1, H2. *)
    (*   red. *)
    (*   destruct (observe i) eqn: Heqi; destruct (observe i0) eqn: Heqi0; *)
    (*     try apply eqit_inv in H1; try apply eqit_inv in H2; cbn in H1, H2; try contradiction; auto. *)
    (*   subst; constructor; auto. *)

    (*   right; eapply CIH; eauto; *)
    (*   rewrite unfold_interp in H1, H2; auto. *)
    (* - pstep. cbn in H1, H2. *)
    (*   rewrite itree_eta in H1, H2. *)
    (*   red. *)
    (*   destruct (observe i) eqn: Heqi; *)
    (*     try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
    (*   subst; constructor; auto. *)
    (*   rewrite unfold_interp in H1. *)
    (*   specialize (IHinterp_PropTF _ _ H1 H2). *)

    (*   punfold IHinterp_PropTF. *)
    (* - pstep. cbn in H1, H2. *)
    (*   rewrite itree_eta in H1, H2. *)
    (*   red. *)
    (*   destruct (observe i0) eqn: Heqi; *)
    (*     try apply eqit_inv in H2; cbn in H2; try contradiction; auto. *)
    (*   subst; constructor; auto. *)
    (*   rewrite unfold_interp in H2. *)
    (*   specialize (IHinterp_PropTF _ _ H1 H2). *)

    (*   punfold IHinterp_PropTF. *)
    (* - pstep. apply bisimulation_is_eq in HT1. *)
    (*   rewrite HT1 in H1. cbn in H1. *)
    (*   destruct (resum IFun A e). *)
    (*   cbn in H1. *)
    (*   repeat setoid_rewrite bind_vis in H1. *)
    (*   apply bisimulation_is_eq in H1. rewrite H1. *)
    (*   econstructor; eauto. *)
    (*   eapply eqit_Vis; intros; inv u. *)
    (* - pstep. cbn in H2, H3. red in H. *)
    (*   rewrite H in H0. *)
    (*   rename H2 into H1. *)
    (*   rename H3 into H2. *)

    (*   rewrite itree_eta in H1, H2. *)
    (*   repeat destruct e; cbn in *. *)
    (*   + rewrite bind_bind in H1. *)
    (*     unfold lift_OOM in H1. *)
    (*     rename H0 into KS. rewrite bind_trigger in KS. *)
    (*     cbn in *. *)
    (*     destruct (EC.DVC.uvalue_convert f) eqn : Hf. *)
    (*     { rewrite bind_ret_l, bind_bind in H1. *)
    (*       destruct *)
    (*         (map_monad_In args *)
    (*           (fun (elt : InterpreterStackBigIntptr.LP.Events.DV.dvalue) (_ : In elt args) => EC.DVC.dvalue_convert elt)) eqn: Hm. *)
    (*       { rewrite bind_ret_l, bind_bind in H1. *)
    (*         rewrite bind_trigger in H1. *)

    (*         destruct (observe i) eqn: Heqi; *)
    (*           try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
    (*         red. *)
    (*         setoid_rewrite Heqi. *)
    (*         destruct H1 as (?&?&?). *)
    (*         dependent destruction x. *)
    (*         red in H, H0. *)
    (*         econstructor; [ constructor | ..]; eauto; cycle 1. *)
    (*         - red; reflexivity. *)
    (*         - cbn in *. *)
    (*           rewrite <- unfold_interp in H2. *)
    (*           rewrite <- itree_eta in H2. *)
    (*           rewrite H2. rewrite KS. rewrite interp_vis. cbn. *)
    (*           rewrite bind_bind. unfold lift_OOM. *)
    (*           rewrite Hf. setoid_rewrite bind_ret_l. *)
    (*           setoid_rewrite bind_bind. rewrite Hm. *)
    (*           setoid_rewrite bind_ret_l. *)
    (*           setoid_rewrite bind_bind. *)
    (*           setoid_rewrite bind_trigger. *)
    (*           unfold subevent. rewrite H0. *)
    (*           eapply eqit_Vis. intros. *)
    (*           Unshelve. *)
    (*           3 : exact (fun u0 : E2.DV.dvalue => *)
    (*           ITree.bind match EC.DVCrev.dvalue_convert u0 with *)
    (*                     | NoOom a0 => ret a0 *)
    (*                     | Oom s => raise_oom s *)
    (*                      end (fun x1 : E1.DV.dvalue => Tau (interp EC.L3_convert (k2 x1)))). *)
    (*           reflexivity. intros. inv H. *)
    (*         - cbn. red in H1. subst. *)
    (*           eapply bisimulation_is_eq in H1. rewrite H1. *)

    (*           destruct (EC.DVCrev.dvalue_convert a) eqn: Ht. *)
    (*           + setoid_rewrite H in HK. subst. *)
    (*             rewrite subevent_subevent in H3. *)
    (*             eapply Returns_uvalue_convert_L3 in H3; eauto. *)
    (*             specialize (HK _ H3). pclearbot. *)
    (*             pose proof @bind_ret_l as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ. *)
    (*             pose proof @bind_ret_l as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ. *)
    (*             pstep; constructor; eauto. right; eauto. *)
    (*             eapply CIH; try rewrite <- unfold_interp; try reflexivity. *)
    (*             eapply HK. *)
    (*           + setoid_rewrite H in HK. subst. *)
    (*             unfold raiseOOM. *)
    (*             pose proof @bind_bind as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ. *)
    (*             pose proof @bind_trigger as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ. *)
    (*             pose proof @bind_bind as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ. *)
    (*             pose proof @bind_trigger as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ. *)
    (*             pstep; econstructor; eauto. unfold subevent. *)
    (*             reflexivity. } *)
    (*       { unfold raiseOOM in H1. rewrite bind_trigger in H1. *)
    (*         red. destruct (observe i) eqn: Heqi; *)
    (*           try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
    (*         destruct H1 as (?&?&?). *)
    (*         dependent destruction x. *)
    (*         red in H, H0. *)
    (*         (* rewrite H1. *) *)
    (*         econstructor; eauto. *)
    (*         - intros. inv a. *)
    (*         - red; reflexivity. *)
    (*         - cbn in *. rewrite <- itree_eta in H2. *)
    (*           rewrite H2. rewrite <- unfold_interp. *)
    (*           rewrite KS. rewrite interp_vis. cbn. *)
    (*           rewrite bind_bind. unfold lift_OOM. *)
    (*           rewrite Hf. setoid_rewrite bind_ret_l. *)
    (*           setoid_rewrite bind_bind. rewrite Hm. *)
    (*           setoid_rewrite bind_trigger. *)
    (*           setoid_rewrite bind_vis. *)
    (*           unfold subevent. rewrite H0. *)
    (*           eapply eqit_Vis. intros. inv u0. } } *)

    (*       unfold raiseOOM in H1. rewrite bind_trigger in H1. *)
    (*       red. destruct (observe i) eqn: Heqi; *)
    (*         try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
    (*       destruct H1 as (?&?&?). *)
    (*       dependent destruction x. *)
    (*       red in H, H0. cbn in *. *)
    (*       econstructor; eauto. *)
    (*     * intros. inv a. *)
    (*     * red; reflexivity. *)
    (*     * rewrite <- itree_eta in H2. rewrite H2. *)
    (*       rewrite <- unfold_interp. rewrite KS. *)
    (*       rewrite interp_vis. *)
    (*       cbn. rewrite bind_bind. unfold lift_OOM. rewrite Hf. *)
    (*       setoid_rewrite bind_trigger. *)
    (*       setoid_rewrite bind_vis. *)
    (*       unfold subevent. rewrite H0. *)
    (*       eapply eqit_Vis. intros. inv u. *)
    (*   + destruct s. *)
    (*     { destruct p. *)
    (*       cbn in *. *)
    (*       destruct (EC.DVC.uvalue_convert x) eqn:Ht. *)
    (*       - cbn in *. *)
    (*         rewrite bind_ret_l in H1. *)
    (*         rewrite bind_trigger in H1. *)
    (*         rewrite bind_vis in H1. *)
    (*         red. *)
    (*         destruct (observe i) eqn: Heqi; *)
    (*           try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
    (*         destruct H1 as (?&?&?). *)
    (*         cbn in *. *)
    (*         dependent destruction x. *)
    (*         red in H, H0. *)
    (*         econstructor; eauto. *)
    (*         repeat red. intros. inv a. *)
    (*         red; reflexivity. *)
    (*         setoid_rewrite <- itree_eta in H2. rewrite H2. *)
    (*         rewrite <- unfold_interp. *)
    (*         rewrite H0. rewrite bind_trigger. *)
    (*         rewrite interp_vis. *)
    (*         cbn. *)
    (*         setoid_rewrite bind_trigger. rewrite bind_vis. cbn in *; subst. eapply eqit_Vis. *)
    (*         intros. inv u. *)

    (*         rewrite bind_trigger in H1. *)


    (*       destruct s; try destruct u; cbn in H1. *)
    (*       -- repeat red in HTA. *)
    (*           unfold raiseUB in H1. rewrite bind_trigger in H1. *)
    (*           red. *)
    (*           destruct (observe i) eqn: Heqi; *)
    (*             try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
    (*           destruct H1 as (?&?&?). *)
    (*           dependent destruction x. *)
    (*           red in H, H0. *)
    (*           econstructor; eauto. *)
    (*           repeat red. intros. inv a. *)
    (*           red; reflexivity. *)
    (*           setoid_rewrite <- itree_eta in H2. rewrite H2. *)
    (*           rewrite <- unfold_interp. *)
    (*           rewrite H0. rewrite bind_trigger. *)
    (*           rewrite interp_vis. *)
    (*           cbn. *)
    (*           setoid_rewrite bind_trigger. rewrite bind_vis. cbn in *; subst. eapply eqit_Vis. *)
    (*           intros. inv u. *)
    (*       -- destruct s; try destruct u; cbn in H1. *)
    (*          ++ destruct d. cbn in H1. *)
    (*             rewrite <- unfold_interp in H2. *)

    (*             rename H0 into KS. *)
    (*             setoid_rewrite bind_trigger in H1. *)
    (*             setoid_rewrite bind_trigger in KS. *)

    (*             red. *)
    (*             destruct (observe i) eqn: Heqi; *)
    (*               try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
    (*             destruct H1 as (?&?&?). *)
    (*             dependent destruction x. *)
    (*             red in H, H0. subst. *)
    (*             assert (Returns tt ta). *)
    (*             { rewrite H. unfold trigger. eapply ReturnsVis; eauto. *)
    (*               unfold subevent. reflexivity. *)
    (*               constructor; reflexivity. } *)
    (*             specialize (HK _ H0). pclearbot. *)
    (*             econstructor; eauto. *)
    (*             ** intros. red in H1. specialize (H1 tt). *)
    (*                eapply bisimulation_is_eq in H1. destruct a. *)
    (*                rewrite H1. *)
    (*                right; eapply CIH. *)
    (*                2 : { rewrite <- interp_tau, <- unfold_interp. reflexivity. } *)
    (*                pstep; econstructor; eauto. punfold HK. *)
    (*                rewrite <- unfold_interp. Unshelve. *)
    (*                16 : exact (fun x => interp EC.L3_convert (k2 x)). reflexivity. *)
    (*                all : shelve. *)
    (*             ** red; reflexivity. *)
    (*             ** rewrite <- itree_eta in H2. *)
    (*                rewrite H2. rewrite KS. *)
    (*                rewrite interp_vis. cbn. unfold debug. *)
    (*                do 2 rewrite bind_trigger. unfold subevent, resum, ReSum_inr. *)
    (*                eapply eqit_Vis. intros. rewrite tau_eutt. reflexivity. *)
    (*          ++ repeat red in HTA. *)
    (*             destruct f. cbn in H1. setoid_rewrite bind_trigger in H1. *)
    (*             red. *)
    (*             destruct (observe i) eqn: Heqi; *)
    (*               try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
    (*             destruct H1 as (?&?&?). *)
    (*             dependent destruction x. *)
    (*             red in H, H0. cbn in *; subst. *)
    (*             econstructor; eauto. *)
    (*             intros. inv a. *)
    (*             red; reflexivity. *)
    (*             setoid_rewrite <- itree_eta in H2. rewrite H2. *)
    (*             rewrite <- unfold_interp. *)
    (*             rewrite H0. cbn. rewrite interp_bind. *)
    (*             rewrite interp_trigger. cbn. unfold LLVMEvents.raise. *)
    (*             do 2 rewrite bind_trigger. rewrite bind_vis. *)
    (*             apply eqit_Vis; intros; inv u. *)


    (*     } *)
    (*     destruct s. *)
    (*     * unfold raiseOOM in H1. *)
    (*       destruct o. *)
    (*       cbn in H1. *)
    (*       rewrite bind_bind, bind_trigger in H1. *)
    (*       rewrite itree_eta in H1, H2. *)
    (*       red. *)
    (*       destruct (observe i) eqn: Heqi; *)
    (*         try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
    (*       destruct H1 as (?&?&?). *)
    (*       dependent destruction x. *)
    (*       red in H, H0. cbn in *. *)
    (*       econstructor; eauto. *)
    (*       -- intros. inv a. *)
    (*       -- red; reflexivity. *)
    (*       -- rewrite <- itree_eta in H2. rewrite H2. *)
    (*          rewrite <- unfold_interp. rewrite H0. *)
    (*          rewrite bind_trigger. *)
    (*          rewrite interp_vis. cbn. do 2 setoid_rewrite bind_trigger. *)
    (*          rewrite bind_vis. subst. *)
    (*          apply eqit_Vis; intros; inv u. *)
    (*     * destruct s; try destruct u; cbn in H1. *)
    (*       -- repeat red in HTA. *)
    (*           unfold raiseUB in H1. rewrite bind_trigger in H1. *)
    (*           red. *)
    (*           destruct (observe i) eqn: Heqi; *)
    (*             try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
    (*           destruct H1 as (?&?&?). *)
    (*           dependent destruction x. *)
    (*           red in H, H0. *)
    (*           econstructor; eauto. *)
    (*           repeat red. intros. inv a. *)
    (*           red; reflexivity. *)
    (*           setoid_rewrite <- itree_eta in H2. rewrite H2. *)
    (*           rewrite <- unfold_interp. *)
    (*           rewrite H0. rewrite bind_trigger. *)
    (*           rewrite interp_vis. *)
    (*           cbn. *)
    (*           setoid_rewrite bind_trigger. rewrite bind_vis. cbn in *; subst. eapply eqit_Vis. *)
    (*           intros. inv u. *)
    (*       -- destruct s; try destruct u; cbn in H1. *)
    (*          ++ destruct d. cbn in H1. *)
    (*             rewrite <- unfold_interp in H2. *)

    (*             rename H0 into KS. *)
    (*             setoid_rewrite bind_trigger in H1. *)
    (*             setoid_rewrite bind_trigger in KS. *)

    (*             red. *)
    (*             destruct (observe i) eqn: Heqi; *)
    (*               try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
    (*             destruct H1 as (?&?&?). *)
    (*             dependent destruction x. *)
    (*             red in H, H0. subst. *)
    (*             assert (Returns tt ta). *)
    (*             { rewrite H. unfold trigger. eapply ReturnsVis; eauto. *)
    (*               unfold subevent. reflexivity. *)
    (*               constructor; reflexivity. } *)
    (*             specialize (HK _ H0). pclearbot. *)
    (*             econstructor; eauto. *)
    (*             ** intros. red in H1. specialize (H1 tt). *)
    (*                eapply bisimulation_is_eq in H1. destruct a. *)
    (*                rewrite H1. *)
    (*                right; eapply CIH. *)
    (*                2 : { rewrite <- interp_tau, <- unfold_interp. reflexivity. } *)
    (*                pstep; econstructor; eauto. punfold HK. *)
    (*                rewrite <- unfold_interp. Unshelve. *)
    (*                16 : exact (fun x => interp EC.L3_convert (k2 x)). reflexivity. *)
    (*                all : shelve. *)
    (*             ** red; reflexivity. *)
    (*             ** rewrite <- itree_eta in H2. *)
    (*                rewrite H2. rewrite KS. *)
    (*                rewrite interp_vis. cbn. unfold debug. *)
    (*                do 2 rewrite bind_trigger. unfold subevent, resum, ReSum_inr. *)
    (*                eapply eqit_Vis. intros. rewrite tau_eutt. reflexivity. *)
    (*          ++ repeat red in HTA. *)
    (*             destruct f. cbn in H1. setoid_rewrite bind_trigger in H1. *)
    (*             red. *)
    (*             destruct (observe i) eqn: Heqi; *)
    (*               try apply eqit_inv in H1; cbn in H1; try contradiction; auto. *)
    (*             destruct H1 as (?&?&?). *)
    (*             dependent destruction x. *)
    (*             red in H, H0. cbn in *; subst. *)
    (*             econstructor; eauto. *)
    (*             intros. inv a. *)
    (*             red; reflexivity. *)
    (*             setoid_rewrite <- itree_eta in H2. rewrite H2. *)
    (*             rewrite <- unfold_interp. *)
    (*             rewrite H0. cbn. rewrite interp_bind. *)
    (*             rewrite interp_trigger. cbn. unfold LLVMEvents.raise. *)
    (*             do 2 rewrite bind_trigger. rewrite bind_vis. *)
    (*             apply eqit_Vis; intros; inv u. *)

    (*             Unshelve. *)
    (*             all : eauto. *)
    (*             all : inv x.     *)
  Abort.

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

  Lemma refine_OOM_h_L4_convert_tree_strict :
    forall {T} x_inf y_inf (RR : relation T),
      refine_OOM_h RR x_inf y_inf ->
      refine_OOM_h RR (L4_convert_tree_strict x_inf) (L4_convert_tree_strict y_inf).
  Proof.
    intros T.

    unfold refine_OOM_h, L4_convert_tree_strict, refine_OOM_h_flip.
    intros.
    eapply interp_prop_oom_l_eutt_Proper; try typeclasses eauto.
    rewrite (unfold_interp y_inf); reflexivity.
    rewrite (unfold_interp x_inf); reflexivity.
    cbn.

    match goal with
    | |- interp_prop_oom_l _ _ _ ?l ?r => remember l as i; remember r as i0
    end.

    assert (i ≅ _interp EC.L4_convert_strict (observe y_inf)). {
      rewrite Heqi. reflexivity.
    } clear Heqi.
    remember (_interp EC.L4_convert_strict (observe x_inf)).
    assert (i0 ≅ _interp EC.L4_convert_strict (observe x_inf)). {
      subst; reflexivity.
    } clear Heqi1 Heqi0.
    revert x_inf y_inf H i i0 H0 H1.

    pcofix CIH.

    intros * H.
    punfold H; red in H.
    remember (observe y_inf) as oy; remember (observe x_inf) as ox.
    clear Heqoy Heqox.

    induction H; pclearbot; intros; subst; auto.
    - pstep. cbn in H1, H2.
      rewrite itree_eta in H1, H2.
      red.
      destruct (observe i) eqn: Heqi; destruct (observe i0) eqn: Heqi0;
        try apply eqit_inv in H1; try apply eqit_inv in H2; cbn in H1, H2; try contradiction; auto.
      subst; constructor; auto.
    - pstep. cbn in H1, H2.
      rewrite itree_eta in H1, H2.
      red.
      destruct (observe i) eqn: Heqi; destruct (observe i0) eqn: Heqi0;
        try apply eqit_inv in H1; try apply eqit_inv in H2; cbn in H1, H2; try contradiction; auto.
      subst; constructor; auto.

      right; eapply CIH; eauto;
      rewrite unfold_interp in H1, H2; auto.
    - pstep. cbn in H1, H2.
      rewrite itree_eta in H1, H2.
      red.
      destruct (observe i) eqn: Heqi;
        try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
      subst; constructor; auto.
      rewrite unfold_interp in H1.
      specialize (IHinterp_prop_oomTF _ _ H1 H2).
      punfold IHinterp_prop_oomTF.
    - pstep. cbn in H1, H2.
      rewrite itree_eta in H1, H2.
      red.
      destruct (observe i0) eqn: Heqi;
        try apply eqit_inv in H2; cbn in H2; try contradiction; auto.
      subst; constructor; auto.
      rewrite unfold_interp in H2.
      specialize (IHinterp_prop_oomTF _ _ H1 H2).
      punfold IHinterp_prop_oomTF.
    - pstep. apply bisimulation_is_eq in HT1.
      rewrite HT1 in H1. cbn in H1.
      destruct (resum IFun A e).
      cbn in H1.
      repeat setoid_rewrite bind_vis in H1.
      apply bisimulation_is_eq in H1. rewrite H1.
      econstructor; eauto.
      eapply eqit_Vis; intros; inv u.
      inv u0.
    - discriminate.
    - pstep. red in HSPEC, KS.
      rewrite HSPEC in KS.

      rewrite itree_eta in H1, H2.
      repeat destruct e; cbn in *.
      + rewrite bind_bind in H1.
        unfold lift_OOM in H1.
        rewrite bind_trigger in KS.
        cbn in *.
        destruct (DVC.uvalue_convert_strict f) eqn : Hf.
        { rewrite bind_ret_l, bind_bind in H1.
          destruct
            (map_monad_In args
              (fun (elt : E1.DV.dvalue) (_ : In elt args) => DVC.dvalue_convert_strict elt)) eqn: Hm.
          { rewrite bind_ret_l, bind_bind in H1.
            rewrite bind_trigger in H1.

            destruct (observe i) eqn: Heqi;
              try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
            red.
            setoid_rewrite Heqi.
            destruct H1 as (?&?&?).
            dependent destruction x.
            red in H, H0.
            econstructor; [ constructor | ..]; eauto; cycle 1.
            - red; reflexivity.
            - cbn in *.
              rewrite <- unfold_interp in H2.
              rewrite <- itree_eta in H2.
              red.
              rewrite H2. rewrite KS. rewrite interp_vis. cbn.
              rewrite bind_bind. unfold lift_OOM.
              rewrite Hf. setoid_rewrite bind_ret_l.
              setoid_rewrite bind_bind. rewrite Hm.
              setoid_rewrite bind_ret_l.
              setoid_rewrite bind_bind.
              setoid_rewrite bind_trigger.
              unfold subevent.
              subst.
              eapply eqit_Vis.
              intros u0.
              Unshelve.
              2: intros [].
              2: exact (fun u0 : E2.DV.dvalue =>
              ITree.bind match DVCrev.dvalue_convert_strict u0 with
                        | NoOom a0 => ret a0
                        | Oom s => raise_oom s
                         end (fun x1 : E1.DV.dvalue => Tau (interp EC.L4_convert_strict (k2 x1)))).
              reflexivity.
            - cbn. subst.
              specialize (H0 a).
              eapply bisimulation_is_eq in H0. subst. rewrite H0.

              destruct (DVCrev.dvalue_convert_strict a) eqn: Ht.
              + setoid_rewrite HSPEC in HK. subst.
                (* TODO: Originally used Returns_uvalue_convert_L0
                applied to H3... But it seems Returns is weird with
                the vis case and allows any value to be
                returned...? *)
                rename H2 into H3'.
                pose proof Returns_ExternalCall_L0 d f t args as H3.
                specialize (HK d).
                forward HK.
                admit.
                pclearbot.
                pose proof @bind_ret_l as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ.
                pose proof @bind_ret_l as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ.
                pstep; constructor; eauto. right; eauto.
                eapply CIH; try rewrite <- unfold_interp; try reflexivity.
                eapply HK.
              + setoid_rewrite HSPEC in HK. subst.
                unfold raiseOOM.
                pose proof @bind_bind as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ.
                pose proof @bind_trigger as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ.
                pose proof @bind_bind as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ.
                pose proof @bind_trigger as HEQ; eapply bisimulation_is_eq in HEQ; rewrite HEQ; clear HEQ.
                pstep; econstructor; eauto. unfold subevent.
                reflexivity. }
          { unfold raiseOOM in H1. rewrite bind_trigger in H1.
            red. destruct (observe i) eqn: Heqi;
              try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
            destruct H1 as (?&?&?).
            dependent destruction x.
            red in H, H0.
            (* rewrite H1. *)
            eapply Interp_Prop_OomT_Vis; eauto.
            - intros. inv a.
            - red; reflexivity.
            - cbn in *.
              rewrite <- unfold_interp in H2.
              rewrite <- itree_eta in H2.
              red.
              rewrite H2. rewrite KS. rewrite interp_vis. cbn.
              rewrite bind_bind. unfold lift_OOM.
              rewrite Hf. setoid_rewrite bind_ret_l.
              setoid_rewrite bind_bind. rewrite Hm.
              setoid_rewrite bind_trigger.
              setoid_rewrite bind_vis.
              unfold subevent.
              subst.
              eapply eqit_Vis. intros. inv u0. } }

          unfold raiseOOM in H1. rewrite bind_trigger in H1.
          red. destruct (observe i) eqn: Heqi;
            try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
          destruct H1 as (?&?&?).
          dependent destruction x.
          red in H, H0. cbn in *.
          inv e.
          observe_vis.
          eapply Interp_Prop_OomT_Vis_OOM_L; eauto.
          reflexivity.
          observe_vis.
          eapply Interp_Prop_OomT_Vis_OOM_L; eauto.
          reflexivity.
      + (* Stdout *)
        admit.
      + (* Stderr *)
        admit.
      + destruct s.
        * unfold raiseOOM in H1.
          destruct o.
          cbn in H1.
          rewrite bind_bind, bind_trigger in H1.
          rewrite itree_eta in H1, H2.
          red.
          destruct (observe i) eqn: Heqi;
            try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
          destruct H1 as (?&?&?).
          dependent destruction x.
          red in H, H0. cbn in *.
          inv e.
          observe_vis.
          eapply Interp_Prop_OomT_Vis_OOM_L; eauto.
          reflexivity.
          observe_vis.
          eapply Interp_Prop_OomT_Vis_OOM_L; eauto.
          reflexivity.
        * destruct s; try destruct u; cbn in H1.
          -- repeat red in HTA.
              unfold raiseUB in H1. rewrite bind_trigger in H1.
              red.
              destruct (observe i) eqn: Heqi;
                try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
              destruct H1 as (?&?&?).
              dependent destruction x.
              red in H, H0.
              eapply Interp_Prop_OomT_Vis; eauto.
              repeat red. intros. inv a.
              red; reflexivity.
              setoid_rewrite <- itree_eta in H2. red. rewrite H2.
              rewrite <- unfold_interp.
              setoid_rewrite KS.
              setoid_rewrite bind_trigger.
              setoid_rewrite interp_vis.
              cbn.
              setoid_rewrite bind_trigger. setoid_rewrite bind_vis. cbn in *; subst. eapply eqit_Vis.
              intros [].
          -- destruct s; try destruct u; cbn in H1.
             ++ destruct d. cbn in H1.
                rewrite <- unfold_interp in H2.

                setoid_rewrite bind_trigger in H1.
                setoid_rewrite bind_trigger in KS.

                red.
                destruct (observe i) eqn: Heqi;
                  try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
                destruct H1 as (?&?&?).
                dependent destruction x.
                red in H, H0. subst.
                assert (Returns tt ta).
                { rewrite HSPEC. unfold trigger. eapply ReturnsVis; eauto.
                  unfold subevent. reflexivity.
                  constructor; reflexivity. }
                specialize (HK _ H). pclearbot.
                eapply Interp_Prop_OomT_Vis; eauto.
                ** intros. specialize (H0 tt).
                   eapply bisimulation_is_eq in H0. destruct a.
                   rewrite H0.
                   right; eapply CIH.
                   2 : { rewrite <- interp_tau, <- unfold_interp. reflexivity. }
                   pstep; econstructor; eauto. punfold HK.
                   rewrite <- unfold_interp. Unshelve.
                   14 : exact (fun x => interp EC.L4_convert_strict (k2 x)). reflexivity.
                   all : shelve.
                ** red; reflexivity.
                ** rewrite <- itree_eta in H2.
                   red.
                   rewrite H2. rewrite KS.
                   rewrite interp_vis. cbn. unfold debug.
                   do 2 rewrite bind_trigger. unfold subevent, resum, ReSum_inr.
                   eapply eqit_Vis. intros. rewrite tau_eutt. reflexivity.
             ++ repeat red in HTA.
                destruct f. cbn in H1. setoid_rewrite bind_trigger in H1.
                red.
                destruct (observe i) eqn: Heqi;
                  try apply eqit_inv in H1; cbn in H1; try contradiction; auto.
                destruct H1 as (?&?&?).
                dependent destruction x.
                red in H, H0. cbn in *; subst.
                eapply Interp_Prop_OomT_Vis; eauto.
                intros. inv a.
                red; reflexivity.
                setoid_rewrite <- itree_eta in H2.
                red.
                rewrite H2.
                rewrite <- unfold_interp.
                rewrite KS.
                cbn. rewrite interp_bind.
                rewrite interp_trigger. cbn. unfold LLVMEvents.raise.
                do 2 rewrite bind_trigger. rewrite bind_vis.
                apply eqit_Vis.
                intros [].

                Unshelve.
                all : eauto.
                all : inv x.
  Abort.

  Lemma refine_OOM_h_L5_convert_tree_strict :
    forall {T} x_inf y_inf (RR : relation T),
      refine_OOM_h RR x_inf y_inf ->
      refine_OOM_h RR (L5_convert_tree_strict x_inf) (L5_convert_tree_strict y_inf).
  Proof.
    intros T.
    (* apply refine_OOM_h_L4_convert_tree_strict. *)
  Abort.

  Lemma refine_OOM_h_L6_convert_tree_strict :
    forall {T} x_inf y_inf (RR : relation T),
      refine_OOM_h RR x_inf y_inf ->
      refine_OOM_h RR (L6_convert_tree_strict x_inf) (L6_convert_tree_strict y_inf).
  Proof.
    intros T.
    (* apply refine_OOM_h_L5_convert_tree_strict. *)
  Abort.

  (** Model *)
  Import DynamicTypes TypToDtyp CFG.

  (*
  Definition event_refine_lazy A B (e1 : IS1.LP.Events.L0 A) (e2 : IS2.LP.Events.L0 B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 (E1.ExternalCall dt1 f1 args1), inl1 (E2.ExternalCall dt2 f2 args2) =>
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
               uvalue_refine_lazy f1 f2 /\
               Forall2 dvalue_refine_lazy args1 args2).
    }

    (* Intrinsics *)
    { apply (dt1 = dt2 /\
               name1 = name2 /\
               Forall2 dvalue_refine_lazy args1 args2).
    }

    (* Globals *)
    { inversion e1.
      - (* Global write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_refine_lazy dv dv0).
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
                   uvalue_refine_lazy dv dv0).
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
        + apply (local_refine_lazy args args0).
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
                 dvalue_refine_lazy a a0).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_refine_lazy a a0 /\
                 uvalue_refine_lazy v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      destruct e2 eqn:HE2.
      apply ((Pre <-> Pre0) /\
               uvalue_refine_lazy x x0).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { apply True.
    }

    (* FailureE *)
    { apply True.
    }
  Defined.
   *)

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
    { destruct e1 as [e1_msg ?].
      destruct e2 as [e2_msg ?].
      exact (e1_msg = e2_msg).
    }

    (* FailureE *)
    { destruct e1 as [e1_msg ?].
      destruct e2 as [e2_msg ?].
      exact (e1_msg = e2_msg).
    }
  Defined.

  (*
  Definition event_converted_lazy A B (e1 : IS1.LP.Events.L0 A) (e2 : IS2.LP.Events.L0 B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 (E1.ExternalCall dt1 f1 args1), inl1 (E2.ExternalCall dt2 f2 args2) =>
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
               uvalue_converted_lazy f1 f2 /\
               Forall2 dvalue_converted_lazy args1 args2).
    }

    (* Intrinsics *)
    { apply (dt1 = dt2 /\
               name1 = name2 /\
               Forall2 dvalue_converted_lazy args1 args2).
    }

    (* Globals *)
    { inversion e1.
      - (* Global write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_converted_lazy dv dv0).
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
                   uvalue_converted_lazy dv dv0).
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
        + apply (local_refine_lazy args args0).
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
                 dvalue_converted_lazy a a0).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_converted_lazy a a0 /\
                 uvalue_converted_lazy v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      destruct e2 eqn:HE2.
      apply ((Pre <-> Pre0) /\
               uvalue_converted_lazy x x0).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { apply True.
    }

    (* FailureE *)
    { apply True.
    }
  Defined.
   *)
  (*
  Definition event_res_refine_lazy A B (e1 : IS1.LP.Events.L0 A) (res1 : A) (e2 : IS2.LP.Events.L0 B) (res2 : B) : Prop.
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
      inv e2.

      apply (t = t0 /\
               uvalue_refine_lazy f f0 /\
               Forall2 dvalue_refine_lazy args args0 /\
               dvalue_refine_lazy res1 res2
            ).
    }

    (* Intrinsics *)
    { inv e1.
      inv e2.
      apply (t = t0 /\
               f = f0 /\
               Forall2 dvalue_refine_lazy args args0 /\
               dvalue_refine_lazy res1 res2
            ).
    }

    (* Globals *)
    { inversion e1; subst.
      - (* Global write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_refine_lazy dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                   dvalue_refine_lazy res1 res2
                ).
    }

    (* Locals *)
    { inversion e1; subst.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_refine_lazy dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                uvalue_refine_lazy res1 res2).
    }

    (* Stack *)
    { inversion e1; subst.
      - (* Stack Push *)
        destruct e2 eqn:HE2.
        + apply (local_refine_lazy args args0).
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
                 dvalue_refine_lazy res1 res2).
      - (* Load *)
        destruct e2 eqn:HE2.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_refine_lazy a a0 /\
                 uvalue_refine_lazy res1 res2).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_refine_lazy a a0 /\
                 uvalue_refine_lazy v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1; subst.
      destruct e2 eqn:HE2.
      destruct res1 as [r1 P1].
      destruct res2 as [r2 P2].
      apply ((Pre <-> Pre0) /\
               uvalue_refine_lazy x x0 /\
               dvalue_refine_lazy r1 r2).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { apply True.
    }

    (* FailureE *)
    { apply True.
    }
  Defined.
  *)

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
    { destruct e1 as [e1_msg ?].
      destruct e2 as [e2_msg ?].
      exact (e1_msg = e2_msg).
    }

    (* FailureE *)
    { destruct e1 as [e1_msg ?].
      destruct e2 as [e2_msg ?].
      exact (e1_msg = e2_msg).
    }
  Defined.

  (*
  Definition L0'_refine_lazy A B (e1 : IS1.LP.Events.L0' A) (e2 : IS2.LP.Events.L0' B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 (E1.Call dt1 f1 args1), inl1 (E2.Call dt2 f2 args2) =>
                _ (* Calls *)
            | inr1 e1, inr1 e2 =>
                event_refine_lazy _ _ e1 e2
            | _, _ =>
                False
            end).

    (* Calls *)
    { (* Doesn't say anything about return value... *)
      apply (dt1 = dt2 /\
               uvalue_refine_lazy f1 f2 /\
               Forall2 uvalue_refine_lazy args1 args2).
    }
  Defined.

  Definition call_refine_lazy (A B : Type) (c1 : IS1.LP.Events.CallE A) (c2 : CallE B) : Prop.
  Proof.
    (* Calls *)
    { (* Doesn't say anything about return value... *)
      inv c1.
      inv c2.
      apply (t = t0 /\
               uvalue_refine_lazy f f0 /\
               Forall2 uvalue_refine_lazy args args0).
    }
  Defined.
   *)

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

  (*
  Definition call_res_refine_lazy (A B : Type) (c1 : IS1.LP.Events.CallE A) (res1 : A) (c2 : CallE B) (res2 : B) : Prop.
  Proof.
    (* Calls *)
    { inv c1.
      inv c2.
      apply (t = t0 /\
               uvalue_refine_lazy f f0 /\
               Forall2 uvalue_refine_lazy args args0 /\
               uvalue_refine_lazy res1 res2).
    }
  Defined.
   *)

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

  (*
  Definition L0'_res_refine_lazy A B (e1 : IS1.LP.Events.L0' A) (res1 : A) (e2 : IS2.LP.Events.L0' B) (res2 : B) : Prop
    := (sum_postrel call_res_refine_lazy event_res_refine_lazy) _ _ e1 res1 e2 res2.
   *)

  Definition L0'_res_refine_strict A B (e1 : IS1.LP.Events.L0' A) (res1 : A) (e2 : IS2.LP.Events.L0' B) (res2 : B) : Prop
    := (sum_postrel call_res_refine_strict event_res_refine_strict) _ _ e1 res1 e2 res2.

  (*
  Definition exp_E_refine_lazy A B (e1 : IS1.LP.Events.exp_E A) (e2 : IS2.LP.Events.exp_E B) : Prop.
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
                   dvalue_refine_lazy dv dv0).
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
                   uvalue_refine_lazy dv dv0).
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
                 dvalue_refine_lazy a a0).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_refine_lazy a a0 /\
                 uvalue_refine_lazy v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      destruct e2 eqn:HE2.
      apply ((Pre <-> Pre0) /\
               uvalue_refine_lazy x x0).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { apply True.
    }

    (* FailureE *)
    { apply True.
    }
  Defined.
   *)

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

  (*
  Definition exp_E_res_refine_lazy A B (e1 : IS1.LP.Events.exp_E A) (res1 : A) (e2 : IS2.LP.Events.exp_E B) (res2 : B) : Prop.
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
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_refine_lazy dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                   dvalue_refine_lazy res1 res2
                ).
    }

    (* Locals *)
    { inversion e1; subst.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_refine_lazy dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                uvalue_refine_lazy res1 res2).
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
                 dvalue_refine_lazy res1 res2).
      - (* Load *)
        destruct e2 eqn:HE2.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_refine_lazy a a0 /\
                 uvalue_refine_lazy res1 res2).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_refine_lazy a a0 /\
                 uvalue_refine_lazy v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1; subst.
      destruct e2 eqn:HE2.
      destruct res1 as [r1 P1].
      destruct res2 as [r2 P2].
      apply ((Pre <-> Pre0) /\
               uvalue_refine_lazy x x0 /\
            dvalue_refine_lazy r1 r2).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { apply True.
    }

    (* FailureE *)
    { apply True.
    }
  Defined.
   *)

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

  (*
  Definition instr_E_res_refine_lazy A B (e1 : IS1.LP.Events.instr_E A) (res1 : A) (e2 : IS2.LP.Events.instr_E B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 e1, inl1 e2 =>
                call_res_refine_lazy _ _ e1 res1 e2 res2
            | inr1 (inl1 e1), inr1 (inl1 e2) =>
                (* Intrinsics *)
                _
            | inr1 (inr1 e1), inr1 (inr1 e2) =>
                exp_E_res_refine_lazy _ _ e1 res1 e2 res2
            | _, _ =>
                False
            end).

    (* Intrinsics *)
    { inv e1.
      inv e2.
      apply (t = t0 /\
               f = f0 /\
               Forall2 dvalue_refine_lazy args args0
            ).
    }
  Defined.
   *)

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

  (*
  Definition L0_E1E2_rutt_lazy t1 t2
    : Prop :=
    rutt
      event_refine_lazy
      event_res_refine_lazy
      dvalue_refine_lazy
      t1 t2.
  *)

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
      (LLVM1.denote_vellvm (DTYPE_I 32%N) "main" LLVM1.main_args (convert_types (mcfg_of_tle p1)))
      (LLVM2.denote_vellvm (DTYPE_I 32%N) "main" LLVM2.main_args (convert_types (mcfg_of_tle p2))).

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

  (*
  Definition event_res_converted_lazy A B (e1 : IS1.LP.Events.L0 A) (res1 : A) (e2 : IS2.LP.Events.L0 B) (res2 : B) : Prop.
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
      inv e2.

      apply (t = t0 /\
               uvalue_converted_lazy f f0 /\
               Forall2 dvalue_converted_lazy args args0 /\
               dvalue_converted_lazy res1 res2
            ).
    }

    (* Intrinsics *)
    { inv e1.
      inv e2.
      apply (t = t0 /\
               f = f0 /\
               Forall2 dvalue_converted_lazy args args0 /\
               dvalue_converted_lazy res1 res2
            ).
    }

    (* Globals *)
    { inversion e1; subst.
      - (* Global write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_converted_lazy dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                   dvalue_converted_lazy res1 res2
                ).
    }

    (* Locals *)
    { inversion e1; subst.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_converted_lazy dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                uvalue_converted_lazy res1 res2).
    }

    (* Stack *)
    { inversion e1; subst.
      - (* Stack Push *)
        destruct e2 eqn:HE2.
        + apply (local_refine_lazy args args0).
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
                 dvalue_converted_lazy res1 res2).
      - (* Load *)
        destruct e2 eqn:HE2.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_converted_lazy a a0 /\
                 uvalue_converted_lazy res1 res2).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_converted_lazy a a0 /\
                 uvalue_converted_lazy v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1; subst.
      destruct e2 eqn:HE2.
      destruct res1 as [r1 P1].
      destruct res2 as [r2 P2].
      apply ((Pre <-> Pre0) /\
               uvalue_converted_lazy x x0 /\
               dvalue_converted_lazy r1 r2).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { apply True.
    }

    (* FailureE *)
    { apply True.
    }
  Defined.
  *)
  (*
  Definition L0'_converted_lazy A B (e1 : IS1.LP.Events.L0' A) (e2 : IS2.LP.Events.L0' B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 (E1.Call dt1 f1 args1), inl1 (E2.Call dt2 f2 args2) =>
                _ (* Calls *)
            | inr1 e1, inr1 e2 =>
                event_refine_lazy _ _ e1 e2
            | _, _ =>
                False
            end).

    (* Calls *)
    { (* Doesn't say anything about return value... *)
      apply (dt1 = dt2 /\
               uvalue_refine_lazy f1 f2 /\
               Forall2 uvalue_refine_lazy args1 args2).
    }
  Defined.
  *)
  (*
  Definition L0'_res_converted_lazy A B (e1 : IS1.LP.Events.L0' A) (res1 : A) (e2 : IS2.LP.Events.L0' B) (res2 : B) : Prop.
  Proof.
    refine (match e1, e2 with
            | inl1 (E1.Call dt1 f1 args1), inl1 (E2.Call dt2 f2 args2) =>
                _ (* Calls *)
            | inr1 e1, inr1 e2 =>
                event_res_converted_lazy _ _ e1 res1 e2 res2
            | _, _ =>
                False
            end).

    (* Calls *)
    { inv c.
      inv c0.

      apply (dt1 = dt2 /\
               uvalue_converted_lazy f1 f2 /\
               Forall2 uvalue_converted_lazy args1 args2 /\
               uvalue_converted_lazy res1 res2
            ).
    }
  Defined.
   *)
  (*
  Definition call_converted_lazy (A B : Type) (c1 : IS1.LP.Events.CallE A) (c2 : CallE B) : Prop.
  Proof.
    (* Calls *)
    { (* Doesn't say anything about return value... *)
      inv c1.
      inv c2.
      apply (t = t0 /\
               uvalue_converted_lazy f f0 /\
               Forall2 uvalue_converted_lazy args args0).
    }
  Defined.
   *)
  (*
  Definition call_res_converted_lazy (A B : Type) (c1 : IS1.LP.Events.CallE A) (res1 : A) (c2 : CallE B) (res2 : B) : Prop.
  Proof.
    (* Calls *)
    { inv c1.
      inv c2.
      apply (t = t0 /\
               uvalue_converted_lazy f f0 /\
               Forall2 uvalue_converted_lazy args args0 /\
               uvalue_converted_lazy res1 res2).
    }
  Defined.

  Definition exp_E_converted_lazy A B (e1 : IS1.LP.Events.exp_E A) (e2 : IS2.LP.Events.exp_E B) : Prop.
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
                   dvalue_converted_lazy dv dv0).
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
                   uvalue_converted_lazy dv dv0).
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
                 dvalue_converted_lazy a a0).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_converted_lazy a a0 /\
                 uvalue_converted_lazy v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1.
      destruct e2 eqn:HE2.
      apply ((Pre <-> Pre0) /\
               uvalue_converted_lazy x x0).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { apply True.
    }

    (* FailureE *)
    { apply True.
    }
  Defined.

  Definition exp_E_res_converted_lazy A B (e1 : IS1.LP.Events.exp_E A) (res1 : A) (e2 : IS2.LP.Events.exp_E B) (res2 : B) : Prop.
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
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   dvalue_converted_lazy dv dv0).
        + apply False.
      - (* Global read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                   dvalue_converted_lazy res1 res2
                ).
    }

    (* Locals *)
    { inversion e1; subst.
      - (* Local write *)
        destruct e2 eqn:HE2.
        + apply (id = id0 /\
                   uvalue_converted_lazy dv dv0).
        + apply False.
      - (* Local read *)
        destruct e2 eqn:HE2.
        + apply False.
        + apply (id = id0 /\
                uvalue_converted_lazy res1 res2).
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
                 dvalue_converted_lazy res1 res2).
      - (* Load *)
        destruct e2 eqn:HE2.
        1-3,5: apply False.
        apply (t = t0 /\
                 dvalue_converted_lazy a a0 /\
                 uvalue_converted_lazy res1 res2).
      - (* Store *)
        destruct e2 eqn:HE2.
        1-4: apply False.

        apply (t = t0 /\
                 dvalue_converted_lazy a a0 /\
                 uvalue_converted_lazy v v0).
    }

    (* PickE *)
    { (* TODO: confirm whether this is sane... *)
      inversion e1; subst.
      destruct e2 eqn:HE2.
      destruct res1 as [r1 P1].
      destruct res2 as [r2 P2].
      apply ((Pre <-> Pre0) /\
               uvalue_converted_lazy x x0 /\
            dvalue_converted_lazy r1 r2).
    }

    (* OOME *)
    { apply True.
    }

    (* UBE *)
    { apply True.
    }

    (* DebugE *)
    { apply True.
    }

    (* FailureE *)
    { apply True.
    }
  Defined.

  Definition L0_E1E2_rutt_converted_lazy t1 t2
    : Prop :=
    rutt
      event_converted_lazy
      event_res_converted_lazy
      dvalue_converted_lazy
      t1 t2.

  Definition model_E1E2_rutt_converted_lazy p1 p2 :=
    L0_E1E2_rutt_converted_lazy
      (LLVM1.denote_vellvm (DTYPE_I 32%N) "main" LLVM1.main_args (convert_types (mcfg_of_tle p1)))
      (LLVM2.denote_vellvm (DTYPE_I 32%N) "main" LLVM2.main_args (convert_types (mcfg_of_tle p2))).

  Lemma allocate_one_E1E2_rutt_converted_lazy_sound :
    forall (m_declarations : list (LLVMAst.declaration dtyp))
      (m_definitions : list (LLVMAst.definition dtyp (cfg dtyp))),
      rutt event_converted_lazy event_res_converted_lazy eq
        (map_monad LLVM1.allocate_declaration (m_declarations ++ map LLVMAst.df_prototype m_definitions))
        (map_monad allocate_declaration (m_declarations ++ map LLVMAst.df_prototype m_definitions)).
  Proof.
  Abort.

  Lemma allocate_global_E1E2_rutt_converted_lazy_sound :
    forall (m_globals : list (LLVMAst.global dtyp)),
      rutt event_converted_lazy event_res_converted_lazy eq
        (map_monad LLVM1.allocate_global m_globals)
        (map_monad allocate_global m_globals).
  Proof.
  Abort.

  Lemma translate_exp_to_L0_E1E2_converted_lazy_rutt :
    forall {R1 R2} {RR : R1 -> R2 -> Prop} t1 t2,
      rutt exp_E_converted_lazy exp_E_res_converted_lazy RR
        t1
        t2 ->
      rutt event_converted_lazy event_res_converted_lazy RR
        (translate IS1.LP.Events.exp_to_L0 t1)
        (translate exp_to_L0 t2).
  Proof.
  Abort.

  Lemma translate_LU_to_exp_lookup_id_rutt_lazy :
    forall id : LLVMAst.ident,
      rutt exp_E_refine_lazy exp_E_res_refine_lazy uvalue_refine_lazy
        (translate IS1.LP.Events.LU_to_exp (IS1.LLVM.D.lookup_id id)) (translate LU_to_exp (lookup_id id)).
  Proof.
    intros id.
    destruct id.
    - cbn.
      repeat rewrite translate_bind.
      repeat rewrite translate_trigger.
      repeat setoid_rewrite translate_ret.

      repeat rewrite bind_trigger.
      apply rutt_Vis;
        [cbn; auto|].

      intros * ?.
      apply rutt_Ret.
      apply dvalue_refine_lazy_dvalue_to_uvalue.
      destruct H.
      auto.
    - cbn.
      repeat rewrite translate_bind.
      repeat rewrite translate_trigger.
      repeat setoid_rewrite translate_ret.

      repeat rewrite bind_trigger.
      apply rutt_Vis;
        [cbn; auto|].

      intros * ?.
      apply rutt_Ret.
      destruct H.
      auto.
  Qed.
   *)

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


Lemma orutt_denote_exp_Zero_initializer:
  forall odt : option dtyp,
    orutt exp_E_refine_strict exp_E_res_refine_strict uvalue_refine_strict
      (IS1.LLVM.D.denote_exp odt LLVMAst.EXP_Zero_initializer)
      (denote_exp odt LLVMAst.EXP_Zero_initializer) (OOM := OOME).
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
    eapply orutt_Ret.
    apply default_dvalue_of_dtyp_dv1_dv2_equiv in Heqs0.
    destruct Heqs0 as [y [Hy HR]].
    rewrite Hy in Heqs1. inversion Heqs1; subst.
    apply dvalue_refine_strict_dvalue_to_uvalue.
    assumption.
Qed.



  Lemma denote_exp_E1E2_orutt :
    forall e odt,
      orutt exp_E_refine_strict
        exp_E_res_refine_strict uvalue_refine_strict
        (IS1.LLVM.D.denote_exp odt e)
        (IS2.LLVM.D.denote_exp odt e)
        (OOM:=OOME).
  Proof.
    intros e.
    induction e using AstLib.exp_ind; intros odt; cbn;
      match goal with
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
      end.

    - apply translate_LU_to_exp_lookup_id_orutt.

    - simplify_expr odt.
      + pose proof (@IX_supported_dec sz)
            as [SUPPORTED | UNSUPPORTED].
        * inv SUPPORTED;
            repeat rewrite map_ret;
            apply orutt_Ret;
            rewrite uvalue_refine_strict_equation;
            reflexivity.
        *  repeat rewrite unsupported_cases_match; auto;
             repeat rewrite Raise.raise_map_itree;
             apply orutt_raise;
             [intros * CONTRA; dependent destruction CONTRA | cbn; auto].
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

    - apply orutt_denote_exp_Zero_initializer.

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

  (*
  Definition function_denotation_converted_lazy : IS1.LLVM.D.function_denotation -> IS2.LLVM.D.function_denotation -> Prop.
  Proof.
    intros d1 d2.
    unfold function_denotation in *.
    unfold IS1.LLVM.D.function_denotation in *.

    refine (forall args1 args2,
               Forall2 uvalue_converted_lazy args1 args2 ->
               rutt L0'_refine_lazy L0'_res_refine_lazy uvalue_converted_lazy
                 (d1 args1)
                 (d2 args2)
           ).
  Defined.
   *)

  (* TODO: Move this to rutt library *)
  Lemma rutt_iter' {E1 E2 I1 I2 R1 R2}
    (RI : I1 -> I2 -> Prop)
    (RR : R1 -> R2 -> Prop)
    (pre : prerel E1 E2) (post : postrel E1 E2)
    (body1 : I1 -> itree E1 (I1 + R1))
    (body2 : I2 -> itree E2 (I2 + R2))
    (rutt_body
      : forall j1 j2, RI j1 j2 -> rutt pre post (sum_rel RI RR) (body1 j1) (body2 j2))
    : forall (i1 : I1) (i2 : I2) (RI_i : RI i1 i2),
      rutt pre post RR (ITree.iter body1 i1) (ITree.iter body2 i2).
  Proof.
    ginit. gcofix CIH. intros.
    specialize (rutt_body i1 i2 RI_i).
    do 2 rewrite unfold_iter.
    eapply gpaco2_uclo; [|eapply rutt_clo_bind|]; eauto with paco.
    econstructor; eauto. intros ? ? [].
    - gstep.
      red; cbn.
      constructor.
      gbase.
      auto.
    - gstep.
      red.
      constructor.
      auto.
  Qed.

  (* TODO: Move this to rutt library *)
  Lemma rutt_iter_gen :
    forall {E1 E2 : Type -> Type} {A B1 B2 : Type} {R : relation A} {S : relationH B1 B2} (pre : prerel E1 E2) (post : postrel E1 E2),
    forall (x : A -> itree E1 (A + B1)) (y : A -> itree E2 (A + B2)),
      (forall x0 y0 : A, R x0 y0 -> rutt pre post (sum_rel R S) (x x0) (y y0)) ->
      forall x0 y0 : A, R x0 y0 -> rutt pre post S (CategoryOps.iter x x0) (CategoryOps.iter y y0).
  Proof.
    intros E1 E2 A B1 B2 R S pre post body1 body2 EQ_BODY x y Hxy.
    eapply rutt_iter'; eauto.
  Qed.


  (* TODO: Move this to rutt library *)
  Lemma orutt_iter' {OOME E1 E2 I1 I2 R1 R2} `{OOM: OOME -< E2}
    (RI : I1 -> I2 -> Prop)
    (RR : R1 -> R2 -> Prop)
    (pre : prerel E1 E2) (post : postrel E1 E2)
    (body1 : I1 -> itree E1 (I1 + R1))
    (body2 : I2 -> itree E2 (I2 + R2))
    (rutt_body
      : forall j1 j2, RI j1 j2 -> orutt pre post (sum_rel RI RR) (body1 j1) (body2 j2) (OOM:=OOME))
    : forall (i1 : I1) (i2 : I2) (RI_i : RI i1 i2),
      orutt pre post RR (ITree.iter body1 i1) (ITree.iter body2 i2) (OOM:=OOME).
  Proof.
    ginit. gcofix CIH. intros.
    specialize (rutt_body i1 i2 RI_i).
    do 2 rewrite unfold_iter.
    eapply gpaco2_uclo; [|eapply orutt_clo_bind|]; eauto with paco.
    econstructor; eauto. intros ? ? [].
    - gstep.
      red; cbn.
      constructor.
      gbase.
      auto.
    - gstep.
      red.
      constructor.
      auto.
  Qed.

  (* TODO: Move this to orutt library *)
  Lemma orutt_iter_gen :
    forall {OOME E1 E2 : Type -> Type} `{OOM: OOME -< E2} {A B1 B2 : Type} {R : relation A} {S : relationH B1 B2} (pre : prerel E1 E2) (post : postrel E1 E2),
    forall (x : A -> itree E1 (A + B1)) (y : A -> itree E2 (A + B2)),
      (forall x0 y0 : A, R x0 y0 -> orutt pre post (sum_rel R S) (x x0) (y y0) (OOM:=OOME)) ->
      forall x0 y0 : A, R x0 y0 -> orutt pre post S (CategoryOps.iter x x0) (CategoryOps.iter y y0) (OOM:=OOME).
  Proof.
    intros OOME E1 E2 OOM A B1 B2 R S pre post body1 body2 EQ_BODY x y Hxy.
    eapply orutt_iter'; eauto.
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

  (* TODO: Move this *)
  (* Lemma Forall2_Forall2_HIn : *)
  (*   forall {A B : Type} (xs : list A) (ys : list B) f, *)
  (*     Forall2 f xs ys -> *)
  (*     Forall2_HIn xs ys (fun a b HIna HInb => f a b). *)
  (* Proof. *)
  (*   intros A B xs ys f H. *)
  (*   induction H; cbn; auto. *)
  (* Qed. *)

  Transparent uvalue_refine_strict.
  Lemma denote_op_orutt_strict :
    forall op,
      orutt exp_E_refine_strict exp_E_res_refine_strict uvalue_refine_strict
        (IS1.LLVM.D.denote_op op)
        (denote_op op)
        (OOM:=OOME).
  Proof.
    intros op.
    destruct op; cbn;
      try
        solve
        [ solve_orutt_raise
        | eapply orutt_bind with (RR:=Forall2 uvalue_refine_strict);
          [ eapply map_monad_orutt;
            intros [e];
            eapply denote_exp_E1E2_orutt
          |
            intros r1 r2 H;
            change uvalue_refine_strict with (fun a b => uvalue_refine_strict a b) in H;
            unfold uvalue_refine_strict in H;
            eapply orutt_Ret;
            apply map_monad_oom_Forall2 in H;
            unfold uvalue_refine_strict;
            cbn;
            rewrite H;
            reflexivity
          ]
        |
          eapply orutt_bind with (RR:=uvalue_refine_strict);
          [eapply denote_exp_E1E2_orutt|];
          intros r1 r2 H;
          eapply orutt_bind with (RR:=uvalue_refine_strict);
          [eapply denote_exp_E1E2_orutt|];
          intros r0 r3 H0;
          apply orutt_Ret;
          unfold uvalue_refine_strict in *;
          cbn;
          rewrite H, H0;
          cbn;
          reflexivity
        |
          eapply orutt_bind with (RR:=uvalue_refine_strict);
          [eapply denote_exp_E1E2_orutt|];
          intros r1 r2 H;
          apply orutt_Ret;
          unfold uvalue_refine_strict in *;
          cbn;
          rewrite H;
          cbn;
          reflexivity
        |
          apply denote_exp_E1E2_orutt
        ].
    - cbn.
      apply translate_LU_to_exp_lookup_id_orutt.
    - apply orutt_Ret. unfold uvalue_refine_strict. cbn.
      rewrite AC1.addr_convert_null; auto.
  Qed.

  (* (* Maybe I can use something like this for uvalue_refine_unique_prop *) *)
  (* Lemma convert_concretize : *)
  (*   uvalue_convert uv1 = uv2 -> *)
  (*   concretize uv2 dv2 -> *)
  (*   (exists t, dv2 = DVALUE_Oom t) (* May need to be a contains OOM predicate *) \/ *)
  (*     (exists dv1, concretize uv1 dv1 /\ *)
  (*               dvalue_convert dv1 = dv2). *)
  (* Qed. *)

  (* Lemma blah : *)
  (*   forall uv1 dv1, *)
  (*     concretize uv1 dv1 -> *)
  (*     concretize (uvalue_convert uv1) (dvalue_convert dv1). *)
  (* Qed. *)

  (* Lemma blah2  : *)
  (*   IS1.LLVM.D.unique_prop uv1 -> unique_prop (uvalue_convert uv1) *)

  (* (* (* Change unique_prop to be a specific dvalue instead of existential? *) *) *)
  (* Require Import Coq.Logic.Classical_Pred_Type. *)
  (* Lemma uvalue_refine_strict_unique_prop_contra : *)
  (*   forall uv1 uv2, *)
  (*     uvalue_refine_strict uv1 uv2 -> *)
  (*     ~ unique_prop uv2 -> ~ IS1.LLVM.D.unique_prop uv1. *)
  (* Proof. *)
  (*   intros uv1 uv2 REF NUNIQUE. *)

  (*   unfold unique_prop in NUNIQUE. *)
  (*   unfold IS1.LLVM.D.unique_prop. *)

  (*   apply all_not_not_ex. *)
  (*   intros dv1 CONTRA. *)

  (*   rewrite uvalue_refine_strict_equation in REF. *)
  (*   eapply not_ex_all_not in NUNIQUE. *)
  (*   apply NUNIQUE. *)
  (* Abort. *)



  (* Definition unique_prop (uv : uvalue) : Prop
    := exists x, concretize uv x /\ forall dv, concretize uv dv -> dv = x. *)

  (* Definition uvalue_refine_strict (uv1 : DV1.uvalue) (uv2 : DV2.uvalue) : Prop
    := uvalue_convert_strict uv1 = NoOom uv2.*)

  (*
    Definition uvalue_concretize_inf_fin_inclusion uv_inf uv_fin :=
      forall dv_inf,
      uvalue-refine_strict uv_inf uv_fin ->
      concretize_inf uv_inf dv_inf ->
      exists dv_fin,
        dvalue_refine_strict dv_inf dv_fin /\
        concretize_fin uv_fin dv_fin.

    Definition uvalue_concretize_fin_inf_inclusion uv_inf uv_fin :=
      forall dv_fin, concretize_fin uv_fin dv_fin ->
      concretize_inf uv_inf (lift_dvalue dv_fin).

    May need lift_dvalue is an injective function.

    Lemma uvalue_concretize_strict_concretize_inclusion :
      forall uv_inf uv_fin,
        uvalue_refine_strict uv_inf uv_fin ->
        uvalue_concretize_fin_inf_inclusion uv_inf uv_fin.

   Should hopefully just be by induction on uv_inf...
   *)

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
      + exists (DVCrev.DV2.DVALUE_Array []).
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
        exists (DVCrev.DV2.DVALUE_Array (a' :: l)).

        cbn.
        rewrite A.
        rewrite Heqo.
        reflexivity.
    - induction elts.
      + exists (DVCrev.DV2.DVALUE_Vector []).
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
        exists (DVCrev.DV2.DVALUE_Vector (a' :: l)).

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


  Lemma fin_to_inf_dvalue_i1 :
    forall x,
      fin_to_inf_dvalue (DVALUE_I1 x) =
        DVCrev.DV2.DVALUE_I1 x.
  Proof.
    intros x.
    unfold fin_to_inf_dvalue.
    break_match_goal; clear Heqs; destruct p; clear e0;
      cbn in e; subst; inv e.
    auto.
  Qed.

  Lemma fin_to_inf_dvalue_i8 :
    forall x,
      fin_to_inf_dvalue (DVALUE_I8 x) =
        DVCrev.DV2.DVALUE_I8 x.
  Proof.
    intros x.
    unfold fin_to_inf_dvalue.
    break_match_goal; clear Heqs; destruct p; clear e0;
      cbn in e; subst; inv e.
    auto.
  Qed.

  Lemma fin_to_inf_dvalue_i16 :
    forall x,
      fin_to_inf_dvalue (DVALUE_I16 x) =
        DVCrev.DV2.DVALUE_I16 x.
  Proof.
    intros x.
    unfold fin_to_inf_dvalue.
    break_match_goal; clear Heqs; destruct p; clear e0;
      cbn in e; subst; inv e.
    auto.
  Qed.

  Lemma fin_to_inf_dvalue_i32 :
    forall x,
      fin_to_inf_dvalue (DVALUE_I32 x) =
        DVCrev.DV2.DVALUE_I32 x.
  Proof.
    intros x.
    unfold fin_to_inf_dvalue.
    break_match_goal; clear Heqs; destruct p; clear e0;
      cbn in e; subst; inv e.
    auto.
  Qed.

  Lemma fin_to_inf_dvalue_i64 :
    forall x,
      fin_to_inf_dvalue (DVALUE_I64 x) =
        DVCrev.DV2.DVALUE_I64 x.
  Proof.
    intros x.
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

  (* TODO: Move this *)
  Lemma sizeof_dtyp_fin_inf :
    forall t,
      IS1.LP.SIZEOF.sizeof_dtyp t = SIZEOF.sizeof_dtyp t.
  Proof.
    (* Need to expose more stuff to be able to prove this *)
  Admitted.

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
    forall elts,
      fin_to_inf_dvalue (DVALUE_Array elts) =
        DVCrev.DV2.DVALUE_Array (map fin_to_inf_dvalue elts).
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
      rewrite map_cons.

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
    forall elts,
      fin_to_inf_dvalue (DVALUE_Vector elts) =
        DVCrev.DV2.DVALUE_Vector (map fin_to_inf_dvalue elts).
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
      rewrite map_cons.

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
      [ rewrite fin_to_inf_dvalue_i1
      | rewrite fin_to_inf_dvalue_i8
      | rewrite fin_to_inf_dvalue_i16
      | rewrite fin_to_inf_dvalue_i32
      | rewrite fin_to_inf_dvalue_i64
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

      rewrite map_length.
      auto.
    - (* Vectors *)
      constructor; eauto.
      { apply Forall_forall; eauto.
        intros x H3.
        apply in_map_iff in H3.
        destruct H3 as (?&?&?); subst.
        eauto.
      }

      rewrite map_length.
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
    forall fields_fin res,
      DVCrev.dvalue_convert_strict (DVALUE_Array fields_fin) = NoOom res ->
      res = (IS1.LP.Events.DV.DVALUE_Array (map fin_to_inf_dvalue fields_fin)).
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
  Lemma dvalue_convert_strict_vector_map :
    forall fields_fin res,
      DVCrev.dvalue_convert_strict (DVALUE_Vector fields_fin) = NoOom res ->
      res = (IS1.LP.Events.DV.DVALUE_Vector (map fin_to_inf_dvalue fields_fin)).
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
  Lemma eval_int_op_i64_fin_inf :
    forall v1 v2 iop res_fin res_inf,
      @eval_int_op err_ub_oom int64 (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@VIntVMemInt int64 VInt64) ToDvalue_Int64
        iop v1 v2 = success_unERR_UB_OOM res_fin ->
      DVCrev.dvalue_convert_strict res_fin = NoOom res_inf ->
      @IS1.LP.Events.DV.eval_int_op err_ub_oom int64
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@IS1.LP.Events.DV.VIntVMemInt int64 IS1.LP.Events.DV.VInt64) IS1.LP.Events.DV.ToDvalue_Int64
        iop v1 v2 = success_unERR_UB_OOM res_inf.
  Proof.
    intros v1 v2 iop res_fin res_inf EVAL CONV.
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
  Lemma eval_int_op_i16_fin_inf :
    forall v1 v2 iop res_fin res_inf,
      @eval_int_op err_ub_oom int16 (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@VIntVMemInt int16 VInt16) ToDvalue_Int16
        iop v1 v2 = success_unERR_UB_OOM res_fin ->
      DVCrev.dvalue_convert_strict res_fin = NoOom res_inf ->
      @IS1.LP.Events.DV.eval_int_op err_ub_oom int16
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@IS1.LP.Events.DV.VIntVMemInt int16 IS1.LP.Events.DV.VInt16) IS1.LP.Events.DV.ToDvalue_Int16
        iop v1 v2 = success_unERR_UB_OOM res_inf.
  Proof.
    intros v1 v2 iop res_fin res_inf EVAL CONV.
    destruct iop.
    1-3:
      try solve
        [ cbn in *;
          repeat break_match_hyp_inv; cbn in *;
          cbn in CONV; inv CONV;
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
  Lemma eval_int_op_i32_fin_inf :
    forall v1 v2 iop res_fin res_inf,
      @eval_int_op err_ub_oom int32 (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@VIntVMemInt int32 VInt32) ToDvalue_Int32
        iop v1 v2 = success_unERR_UB_OOM res_fin ->
      DVCrev.dvalue_convert_strict res_fin = NoOom res_inf ->
      @IS1.LP.Events.DV.eval_int_op err_ub_oom int32
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@IS1.LP.Events.DV.VIntVMemInt int32 IS1.LP.Events.DV.VInt32) IS1.LP.Events.DV.ToDvalue_Int32
        iop v1 v2 = success_unERR_UB_OOM res_inf.
  Proof.
    intros v1 v2 iop res_fin res_inf EVAL CONV.
    destruct iop.
    1-3:
      try solve
        [ cbn in *;
          repeat break_match_hyp_inv; cbn in *;
          cbn in CONV; inv CONV;
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
  Lemma eval_int_op_i8_fin_inf :
    forall v1 v2 iop res_fin res_inf,
      @eval_int_op err_ub_oom int8 (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@VIntVMemInt int8 VInt8) ToDvalue_Int8
        iop v1 v2 = success_unERR_UB_OOM res_fin ->
      DVCrev.dvalue_convert_strict res_fin = NoOom res_inf ->
      @IS1.LP.Events.DV.eval_int_op err_ub_oom int8
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@IS1.LP.Events.DV.VIntVMemInt int8 IS1.LP.Events.DV.VInt8) IS1.LP.Events.DV.ToDvalue_Int8
        iop v1 v2 = success_unERR_UB_OOM res_inf.
  Proof.
    intros v1 v2 iop res_fin res_inf EVAL CONV.
    destruct iop.
    1-3:
      try solve
        [ cbn in *;
          repeat break_match_hyp_inv; cbn in *;
          cbn in CONV; inv CONV;
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
  Lemma eval_int_op_i1_fin_inf :
    forall v1 v2 iop res_fin res_inf,
      @eval_int_op err_ub_oom int1 (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@VIntVMemInt int1 VInt1) ToDvalue_Int1
        iop v1 v2 = success_unERR_UB_OOM res_fin ->
      DVCrev.dvalue_convert_strict res_fin = NoOom res_inf ->
      @IS1.LP.Events.DV.eval_int_op err_ub_oom int1
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@IS1.LP.Events.DV.VIntVMemInt int1 IS1.LP.Events.DV.VInt1) IS1.LP.Events.DV.ToDvalue_Int1
        iop v1 v2 = success_unERR_UB_OOM res_inf.
  Proof.
    intros v1 v2 iop res_fin res_inf EVAL CONV.
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
        ].
  Qed.

  (* TODO: Move this *)
  Lemma eval_int_op_iptr_fin_inf :
    forall v1_fin v2_fin v1_inf v2_inf iop res_fin res_inf,
      @eval_int_op err_ub_oom IP.intptr (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
        VMemInt_intptr' ToDvalue_intptr
        iop v1_fin v2_fin = success_unERR_UB_OOM res_fin ->
      IS1.LP.IP.from_Z (IP.to_Z v1_fin) = NoOom v1_inf ->
      IS1.LP.IP.from_Z (IP.to_Z v2_fin) = NoOom v2_inf ->
      DVCrev.dvalue_convert_strict res_fin = NoOom res_inf ->
      @IS1.LP.Events.DV.eval_int_op err_ub_oom IS1.LP.IP.intptr
        (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
        (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
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

        epose proof VMEM_REF.mmul_refine _ _ _ v1_inf v2_inf V1 V2 HMUL as (?&?&?).
        rewrite H0 in Heqo.
        rewrite IS1.LP.IP.to_Z_from_Z in Heqo.
        inv Heqo.
        repeat setoid_rewrite H. cbn.
        break_match_goal; try reflexivity.
        setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
        setoid_rewrite dtyp_eqb_refl.
        break_match_goal; try reflexivity.

        (* Contradiction, but need to know something about munsigned *)
        admit.
      }

      break_match_hyp_inv.

      { remember (lift_OOM (mmul v1_fin v2_fin)) as mul_result.
        destruct_err_ub_oom mul_result; inv H0.
        symmetry in Heqmul_result.
        destruct (mmul v1_fin v2_fin) eqn:HMUL; inv Heqmul_result.

        cbn in CONV.
        move CONV after Heqb.
        break_match_hyp_inv.

        epose proof VMEM_REF.mmul_refine _ _ _ v1_inf v2_inf V1 V2 HMUL as (?&?&?).
        rewrite H0 in Heqo.
        rewrite IS1.LP.IP.to_Z_from_Z in Heqo.
        inv Heqo.
        repeat setoid_rewrite H. cbn.
        break_match_goal; try reflexivity.
        setoid_rewrite IS1.LP.IP.VMemInt_intptr_dtyp.
        setoid_rewrite dtyp_eqb_refl.
        break_match_goal; try reflexivity.

        (* Contradiction, but need to know something about munsigned *)
        admit.
      }

      admit.
    - (* Shl *)
      cbn in *.
      destruct (mshl v1_fin v2_fin) eqn:HSHL;
        cbn in *; inv EVAL.

      epose proof VMEM_REF.mshl_refine _ _ _ v1_inf v2_inf V1 V2 HSHL as (?&?&?).
      setoid_rewrite H; cbn in *.

      admit.
    - (* UDiv *)
      admit.
    - (* SDiv *)
      admit.
    - (* LShr *)
      admit.
    - (* AShr *)
      admit.
    - (* URem *)
      admit.
    - (* SRem *)
      admit.
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
  Admitted.

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
    eval_int_op_i1_fin_inf
    eval_int_op_i8_fin_inf
    eval_int_op_i16_fin_inf
    eval_int_op_i32_fin_inf
    eval_int_op_i64_fin_inf
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
      cbn;
      try setoid_rewrite Heqb; eauto with EVAL_INT_FIN_INF.

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

  Lemma eval_int_icmp_fin_inf :
    forall {Int} {VMInt : VellvmIntegers.VMemInt Int} icmp a b,
      DVCrev.dvalue_convert_strict (@eval_int_icmp Int VMInt icmp a b) =
        NoOom
          (@IS1.LP.Events.DV.eval_int_icmp Int VMInt icmp a b).
  Proof.
    intros Int VMInt icmp a b.
    unfold eval_int_icmp, IS1.LP.Events.DV.eval_int_icmp.
    destruct icmp;
      try solve
        [ break_match_goal;
          cbn; auto
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
    unfold eval_icmp in EVAL.
    (* Nasty case analysis... *)
    break_match_hyp_inv;
      try solve
        [ (* Simple integer cases *)
          break_match_hyp_inv;
          [ unfold fin_to_inf_dvalue;

            break_match_goal; clear Heqs;
            destruct p; clear e0;
            cbn in *; inv e;

            break_match_goal; clear Heqs;
            destruct p; clear e0;
            cbn in *; inv e;

            break_match_goal; clear Heqs;
            destruct p; clear e0;
            cbn;

            rewrite eval_int_icmp_fin_inf in e; inv e;
            reflexivity
          | unfold fin_to_inf_dvalue;

            break_match_goal; clear Heqs;
            destruct p; clear e0;
            cbn in *; inv e;

            break_match_goal; clear Heqs;
            destruct p; clear e0;
            cbn in *; inv e;

            cbn;
            reflexivity
          ]
        | (* Ill-typed cases *)
          break_match_hyp_inv
        ].

    { (* dv1: addr *)
      break_match_hyp_inv.
      unfold fin_to_inf_dvalue.

      break_match_goal; clear Heqs.
      destruct p; clear e0.
      cbn in *.
      break_match_hyp_inv.

      break_match_goal; clear Heqs.
      destruct p; clear e0.
      cbn in *.
      break_match_hyp_inv.

      break_match_goal; clear Heqs.
      destruct p; clear e0.
      cbn.

      erewrite AC2.addr_convert_ptoi in e; eauto.
      erewrite AC2.addr_convert_ptoi in e; eauto.

      rewrite eval_int_icmp_fin_inf in e; inv e.
      reflexivity.
    }

    { (* dv1: iptr *)
      break_match_hyp_inv.
      unfold fin_to_inf_dvalue.

      break_match_goal; clear Heqs.
      destruct p; clear e0.
      cbn in *; inv e.

      break_match_goal; clear Heqs.
      destruct p; clear e0.
      cbn in *; inv e.

      break_match_goal; clear Heqs.
      destruct p; clear e0.
      cbn.

      repeat break_match_hyp_inv.

      (* TODO: Annoying intptr differences... *)
      (* NOTE: different implicit arguments *)
      rewrite eval_int_icmp_fin_inf in e; inv e.
      pose proof IS1.LP.IP.to_Z_from_Z i.
      pose proof IS1.LP.IP.from_Z_injective _ _ _ Heqo H.
      rewrite H0 in Heqo.
      cbn.
      unfold IS1.LP.Events.DV.eval_int_icmp.
      admit.
    }

    { (* dv1: poison *)
      break_match_hyp_inv;
        unfold fin_to_inf_dvalue;

        break_match_goal; clear Heqs;
        destruct p; clear e0;
        cbn in *; inv e;

        break_match_goal; clear Heqs;
        destruct p; clear e0;
        cbn in *; inv e;

        cbn;
        reflexivity.
    }
  Admitted.

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

  (* TODO: Move this *)
  Lemma bit_sizeof_dtyp_fin_inf :
    forall t,
      IS1.LP.SIZEOF.bit_sizeof_dtyp t = SIZEOF.bit_sizeof_dtyp t.
  Proof.
  Admitted.

  Lemma get_conv_case_pure_fin_inf:
    forall conv t_from dv t_to res,
      get_conv_case conv t_from dv t_to = Conv_Pure res ->
      IS1.LLVM.MEM.CP.CONC.get_conv_case conv t_from (fin_to_inf_dvalue dv) t_to = IS1.LP.Events.DV.Conv_Pure (fin_to_inf_uvalue res).
  Proof.
    intros conv t_from dv t_to res CONV.
    destruct conv.
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
      repeat break_match_hyp_inv.
      remember (StateMonad.evalStateT
                     (IS1.LLVM.MEM.CP.CONC.MemHelpers.serialize_sbytes
                        (IS1.LP.Events.DV.dvalue_to_uvalue (fin_to_inf_dvalue dv)) t_from) 0) as ser_res.

      (* destruct t_to; inv Heqser_res. *)
      (* - unfold MemHelpers.deserialize_sbytes in *. *)
      (*   (* Not necessarily the same type *) *)
      (*   erewrite from_ubytes_to_ubytes in Heqsb. *)


      (* destruct_err_ub_oom ser_res; cbn; subst. *)
      (* 1-3: exfalso. *)
      (* subst. *)
      (* destruct unERR_UB_OOM. *)
      (* do 3 destruct unEitherT. *)
      (* destruct unIdent; *)
      (*   inv Heqs; *)
      (*   unfold StateMonad.evalStateT; *)
      (*   cbn. *)
      admit.
      admit.
    }

    { (* Addrspacecast *)
      cbn in *;
        repeat break_match_hyp_inv;
        unfold fin_to_inf_dvalue;
        unfold fin_to_inf_uvalue;
        break_match_goal; inv CONV.
    }
  Admitted.

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

  Lemma handle_gep_h_fin_inf :
    forall idxs_fin idxs_inf t base res,
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
                    auto].

      { (* Structs *)
        cbn; rewrite_fin_to_inf_dvalue.
        break_match_hyp_inv.
        rewrite H0.
        erewrite IHidxs_fin; eauto.
        cbn.
        replace (fun (acc : Z) (t : dtyp) => (acc + Z.of_N (IS1.LP.SIZEOF.sizeof_dtyp t))%Z) with
          (fun (acc : Z) (t : dtyp) => (acc + Z.of_N (SIZEOF.sizeof_dtyp t))%Z); eauto.

        apply FunctionalExtensionality.functional_extensionality.
        intros.
        apply FunctionalExtensionality.functional_extensionality.
        intros.
        rewrite sizeof_dtyp_fin_inf.
        auto.
      }

      { (* Packed structs *)
        cbn; rewrite_fin_to_inf_dvalue.
        break_match_hyp_inv.
        rewrite H0.
        erewrite IHidxs_fin; eauto.
        cbn.
        replace (fun (acc : Z) (t : dtyp) => (acc + Z.of_N (IS1.LP.SIZEOF.sizeof_dtyp t))%Z) with
          (fun (acc : Z) (t : dtyp) => (acc + Z.of_N (SIZEOF.sizeof_dtyp t))%Z); eauto.

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

  Lemma addr_convert_int_to_ptr :
    forall base_addr_fin base_addr_inf res_addr_fin res_addr_inf z
      (CONV_BASE : AC2.addr_convert base_addr_fin = NoOom base_addr_inf)
      (CONV_RES : AC2.addr_convert res_addr_fin = NoOom res_addr_inf)
      (ITP : ITOP.int_to_ptr z (PROV.address_provenance base_addr_fin) = NoOom res_addr_fin),
      (IS1.LP.ITOP.int_to_ptr z (IS1.LP.PROV.address_provenance base_addr_inf)) = ret res_addr_inf.
  Proof.
    (* Need to expose more and have some relation between int_to_ptrs / provenances *)
    intros base_addr_fin base_addr_inf res_addr_fin res_addr_inf z CONV_BASE CONV_RES ITP.
  Admitted.

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
      break_match_hyp_inv; rewrite_fin_to_inf_dvalue;
        break_match_hyp_inv;
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
      { (* i32 index *)
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

            assert (exists x1, Int32.signed x1 = Z.pred (Z.pos p')) as (x1 & X1).
            { exists (DVCrev.DV1.repr (Z.pred (Z.pos p'))).
              pose proof Int32.min_signed_neg.
              rewrite Int32.signed_repr; eauto.
              pose proof Int32.signed_range x0.
              lia.
            }

            specialize (IHelts x1 res).
            forward IHelts.
            { rewrite X1.
              cbn.
              destruct p'; cbn; auto.
            }

            unfold fin_to_inf_dvalue in IHelts.
            move IHelts after X1.
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
                inv H3;
                rewrite X1 in H2.
                rewrite X1.

                cbn in H2.
                inv Heqo.
                destruct p'; cbn in *; eauto.
              }

              { move Heqd0 after H2.
                break_match_hyp_inv; clear Heqs; destruct p; clear e1;
                  cbn in e0; inv e0.
                inv H3.
              }
            }

            { move Heqd0 after H0;
                break_match_hyp_inv; clear Heqs; destruct p; clear e1;
                cbn in e0;
                break_match_hyp_inv.
              inv H3.
            }
      }

      { (* i64 index *)
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
            rewrite e in e0.
            inv e0.
            auto.
          + (* Index positive *)
            unfold fin_to_inf_dvalue.
            rename p into p'.

            break_match_goal;
              break_match_hyp; clear Heqs; destruct p; clear e0;
              cbn in e; inv e;
              break_match_hyp_inv.

            break_match_goal;
              break_match_hyp; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; inv H0.

            destruct (dvalue_convert_strict_fin_inf_succeeds res).
            break_match_hyp_inv.
            cbn; rewrite Heqz.
            break_match_hyp_inv.
            cbn.

            assert (exists x1, Int64.signed x1 = Z.pred (Z.pos p')) as (x1 & X1).
            { exists (DVCrev.DV1.repr (Z.pred (Z.pos p'))).
              pose proof Int64.min_signed_neg.
              rewrite Int64.signed_repr; eauto.
              pose proof Int64.signed_range x0.
              lia.
            }

            specialize (IHelts x1 res).
            forward IHelts.
            { rewrite X1.
              cbn.
              destruct p'; cbn; auto.
            }

            unfold fin_to_inf_dvalue in IHelts.
            move IHelts after X1.
            break_match_hyp_inv.
            { move Heqd0 after H0.
              break_match_hyp_inv; clear Heqs; destruct p; clear e1;
                cbn in e0; inv e0.
              break_match_hyp_inv.

              break_match_hyp_inv.
              { move Heqd0 after H2.
                break_match_hyp_inv; clear Heqs; destruct p; clear e1;
                  cbn in e0; inv e0;
                  inv H3.
              }

              { move Heqd0 after H2.
                break_match_hyp_inv; clear Heqs; destruct p; clear e1;
                  cbn in e0; inv e0;
                  inv H3.

                destruct (dvalue_convert_strict_fin_inf_succeeds res).
                rewrite e in e0; inv e0.
                rewrite X1 in H2.
                rewrite X1.

                cbn in H2.
                inv Heqo.
                destruct p'; cbn in *; eauto.
              }
            }

            { move Heqd0 after H0;
                break_match_hyp_inv; clear Heqs; destruct p; clear e1;
                cbn in e0;
                break_match_hyp_inv; inv H3.
            }
      }
    }

    { (* Vectors *)
      break_match_hyp_inv.
      { (* i32 index *)
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

            assert (exists x1, Int32.signed x1 = Z.pred (Z.pos p')) as (x1 & X1).
            { exists (DVCrev.DV1.repr (Z.pred (Z.pos p'))).
              pose proof Int32.min_signed_neg.
              rewrite Int32.signed_repr; eauto.
              pose proof Int32.signed_range x0.
              lia.
            }

            specialize (IHelts x1 res).
            forward IHelts.
            { rewrite X1.
              cbn.
              destruct p'; cbn; auto.
            }

            unfold fin_to_inf_dvalue in IHelts.
            move IHelts after X1.
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
                inv H3;
                rewrite X1 in H2.
                rewrite X1.

                cbn in H2.
                inv Heqo.
                destruct p'; cbn in *; eauto.
              }

              { move Heqd0 after H2.
                break_match_hyp_inv; clear Heqs; destruct p; clear e1;
                  cbn in e0; inv e0.
                inv H3.
              }
            }
      }

      { (* i64 index *)
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
            rewrite e in e0.
            inv e0.
            auto.
          + (* Index positive *)
            unfold fin_to_inf_dvalue.
            rename p into p'.

            break_match_goal;
              break_match_hyp; clear Heqs; destruct p; clear e0;
              cbn in e; inv e;
              break_match_hyp_inv.

            break_match_goal;
              break_match_hyp; clear Heqs; destruct p; clear e0;
              cbn in e; inv e; inv H0.

            destruct (dvalue_convert_strict_fin_inf_succeeds res).
            break_match_hyp_inv.
            cbn; rewrite Heqz.
            break_match_hyp_inv.
            cbn.

            assert (exists x1, Int64.signed x1 = Z.pred (Z.pos p')) as (x1 & X1).
            { exists (DVCrev.DV1.repr (Z.pred (Z.pos p'))).
              pose proof Int64.min_signed_neg.
              rewrite Int64.signed_repr; eauto.
              pose proof Int64.signed_range x0.
              lia.
            }

            specialize (IHelts x1 res).
            forward IHelts.
            { rewrite X1.
              cbn.
              destruct p'; cbn; auto.
            }

            unfold fin_to_inf_dvalue in IHelts.
            move IHelts after X1.
            break_match_hyp_inv.

            { move Heqd0 after H0;
                break_match_hyp_inv; clear Heqs; destruct p; clear e1;
                cbn in e0;
                break_match_hyp_inv; inv H3.
            }

            { move Heqd0 after H0.
              break_match_hyp_inv; clear Heqs; destruct p; clear e1;
                cbn in e0; inv e0.
              break_match_hyp_inv.

              break_match_hyp_inv.
              { move Heqd0 after H2.
                break_match_hyp_inv; clear Heqs; destruct p; clear e1;
                  cbn in e0; inv e0;
                  inv H3.
              }

              { move Heqd0 after H2.
                break_match_hyp_inv; clear Heqs; destruct p; clear e1;
                  cbn in e0; inv e0;
                  inv H3.

                destruct (dvalue_convert_strict_fin_inf_succeeds res).
                rewrite e in e0; inv e0.
                rewrite X1 in H2.
                rewrite X1.

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
      (fix loop (acc elts : list dvalue) (i : LLVMAst.int) {struct elts} :
        option (list dvalue) :=
         match elts with
         | [] => None
         | h :: tl =>
             if (i =? 0)%Z then Some (acc ++ v :: tl) else loop (acc ++ [h]) tl (i - 1)%Z
         end) acc elts idx = ret res ->
      (fix loop (acc elts : list DVCrev.DV2.dvalue) (i : LLVMAst.int) {struct elts} :
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
      + destruct elts as [(b&elts)|]; try discriminate.
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
      (fix loop (acc elts : list dvalue) (i : LLVMAst.int) {struct elts} :
        option (list dvalue) :=
         match elts with
         | [] => None
         | h :: tl =>
             if (i =? 0)%Z then Some (acc ++ v :: tl) else loop (acc ++ [h]) tl (i - 1)%Z
         end) acc elts idx = None ->
      (fix loop (acc elts : list DVCrev.DV2.dvalue) (i : LLVMAst.int) {struct elts} :
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
      { (* i32 index *)
        rewrite fin_to_inf_dvalue_array.
        rewrite fin_to_inf_dvalue_i32.
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

      { (* i64 index *)
        rewrite fin_to_inf_dvalue_array.
        rewrite fin_to_inf_dvalue_i64.
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
      { (* i32 index *)
        rewrite fin_to_inf_dvalue_vector.
        rewrite fin_to_inf_dvalue_i32.
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

      { (* i64 index *)
        rewrite fin_to_inf_dvalue_vector.
        rewrite fin_to_inf_dvalue_i64.
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
      (fix loop (acc elts:list dvalue) (i:LLVMAst.int) :=
        match elts with
        | [] => raise_error "insert_into_str: index out of bounds"
        | h :: tl =>
          (if i =? 0 then ret (acc ++ (v :: tl))
          else loop (acc ++ [h]) tl (i-1))%Z
        end%list) acc elts i = res ->
      (fix loop (acc elts:list DVCrev.DV2.dvalue) (i:LLVMAst.int) :=
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
      | DVALUE_I1 i =>
          if (Int1.unsigned i =? 1)%Z
          then fun y : err_ub_oom dvalue => success_unERR_UB_OOM d = y
          else fun y : err_ub_oom dvalue => success_unERR_UB_OOM d0 = y
      | DVALUE_Poison t => fun y : err_ub_oom dvalue => success_unERR_UB_OOM (DVALUE_Poison t) = y
      | _ =>
          fun ue : err_ub_oom dvalue =>
            ERR_unERR_UB_OOM
              "concretize_uvalueM: ill-typed select, condition in vector was not poison or i1." = ue
      end x ->
      match fin_to_inf_dvalue a with
      | E1.DV.DVALUE_I1 i =>
          if (Int1.unsigned i =? 1)%Z
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
                | DVALUE_I1 i =>
                    if (Int1.unsigned i =? 1)%Z
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
                | IS1.LP.Events.DV.DVALUE_I1 i =>
                    if (Int1.unsigned i =? 1)%Z
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
           | _ => False
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
           | _ => False
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
      rewrite fin_to_inf_dvalue_i1.

      break_match.
      - eapply IH1; eauto.
      - eapply IH2; eauto.
    }

    14: { (* Vector conditional *)
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

        exists (ret (fin_to_inf_dvalue (DVALUE_Poison t))).
        exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 (DVALUE_Poison t)))).

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

        exists (ret (fin_to_inf_dvalue (DVALUE_Vector elts0))).
        exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 (DVALUE_Vector elts0)))).

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

        exists (ret (fin_to_inf_dvalue (DVALUE_Poison t))).
        exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 (DVALUE_Poison t)))).

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
      remember (x2 (DVALUE_Vector elts2_fin)) as x2elts.
      destruct_err_ub_oom x2elts; inv H5.
      cbn in H1.

      repeat red.
      exists (ret (fin_to_inf_dvalue (DVALUE_Vector elts1_fin))).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 (DVALUE_Vector elts1_fin)))).
      cbn; rewrite <- H1; cbn.
      split; eauto.
      split; eauto.

      right; intros a ?; subst.
      repeat red.
      exists (ret (fin_to_inf_dvalue (DVALUE_Vector elts2_fin))).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 (DVALUE_Vector elts2_fin)))).
      cbn; rewrite <- Heqx2elts; cbn.
      split; eauto.
      split; eauto.

      right; intros a ?; subst.
      do 2 rewrite fin_to_inf_dvalue_vector.
      repeat red.
      exists (fmap (map fin_to_inf_dvalue) x).
      exists (fun elts => ret (IS1.LP.Events.DV.DVALUE_Vector elts)).
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

  (* This may not be true. Consider addition... Could OOM in finite
  version... Does not mean the infinite version OOMs *)
  (* Lemma uvalue_concretize_strict_concretize_u_inclusion : *)
  (*   forall uv_inf uv_fin, *)
  (*     uvalue_refine_strict uv_inf uv_fin -> *)
  (*     uvalue_concretize_u_fin_inf_inclusion uv_inf uv_fin. *)
  (* Proof. *)
  (*   (* May not be true *) *)
  (*   intros uv_inf. *)
  (*   induction uv_inf; intros uv_fin REF; *)
  (*     try solve *)
  (*       [ red; intros dv_fin CONC_FIN; *)
  (*         red in REF; *)
  (*         cbn in REF; inv REF; *)

  (*         red in CONC_FIN; *)
  (*         rewrite CONCBASE.concretize_uvalueM_equation in CONC_FIN; *)
  (*         cbn in CONC_FIN; inversion CONC_FIN; subst; *)

  (*         red; *)
  (*         rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation; *)
  (*         cbn; *)
  (*         unfold fin_to_inf_dvalue; *)
  (*         break_match_goal; clear Heqs; destruct p; clear e0; *)
  (*           cbn in e; inv e; *)
  (*         reflexivity *)
  (*       ]. *)
  (*   - (* Addresses *) *)
  (*     red; intros dv_fin CONC_FIN. *)
  (*     red in REF. *)
  (*     cbn in REF. *)
  (*     break_match_hyp_inv. *)
  (*     red in CONC_FIN. *)
  (*     rewrite CONCBASE.concretize_uvalueM_equation in CONC_FIN. *)
  (*     cbn in CONC_FIN; inv CONC_FIN. *)

  (*     red. *)
  (*     rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation. *)
  (*     cbn. *)
  (*     unfold fin_to_inf_dvalue. *)
  (*     break_match_goal. *)
  (*     clear Heqs; destruct p; clear e0. *)
  (*     cbn in e. *)
  (*     break_match_hyp_inv. *)
  (*     pose proof (addr_convert_safe _ _ Heqo0). *)
  (*     pose proof (AC1.addr_convert_injective _ _ _ Heqo H0); subst. *)
  (*     reflexivity. *)
  (*   - (* IPTR *) *)
  (*     red; intros dv_fin CONC_FIN. *)
  (*     red in REF. *)
  (*     cbn in REF. *)
  (*     break_match_hyp_inv. *)

  (*     red. *)
  (*     rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation. *)
  (*     cbn. *)
  (*     unfold fin_to_inf_dvalue. *)
  (*     cbn in CONC_FIN; subst. *)
  (*     cbn. *)
  (*     break_match_goal. *)
  (*     cbn in *. *)
  (*     clear Heqs; destruct p; clear e0. *)
  (*     cbn in e. *)
  (*     break_match_hyp_inv. *)
  (*     pose proof (intptr_convert_safe _ _ Heqo0). *)
  (*     pose proof IP.from_Z_injective _ _ _ Heqo H. *)
  (*     apply IS1.LP.IP.to_Z_inj in H0; subst. *)
  (*     reflexivity. *)
  (*   - (* Undef *) *)
  (*     red; intros dv_fin CONC_FIN. *)
  (*     red in REF. *)
  (*     cbn in REF; inv REF. *)

  (*     red in CONC_FIN. *)
  (*     rewrite CONCBASE.concretize_uvalueM_equation in CONC_FIN. *)
  (*     cbn in CONC_FIN. *)

  (*     red. *)
  (*     rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation. *)
  (*     cbn. *)

  (*     repeat break_match_hyp; try contradiction. *)
  (*     destruct CONC_FIN. *)
  (*     split. *)
  (*     eapply dvalue_has_dtyp_fin_to_inf_dvalue; eauto. *)
  (*     eapply fin_to_inf_dvalue_not_poison; auto. *)

  (*   - (* Struct *) *)
  (*     red; intros dv_fin CONC_FIN. *)
  (*     red in REF. *)
  (*     cbn in REF. *)
  (*     break_match_hyp_inv. *)

  (*     unfold uvalue_concretize_fin_inf_inclusion in H. *)
  (*     apply map_monad_oom_Forall2 in Heqo. *)

  (*     red. *)
  (*     rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation. *)

  (*     red in CONC_FIN. *)
  (*     rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN. *)

  (*     repeat red in CONC_FIN. *)
  (*     destruct CONC_FIN as (?&?&?&?&?). *)

  (*     destruct_err_ub_oom x; cbn in H1; inv H1. *)
  (*     { (* OOM *) *)
  (*       clear H2 H3. *)
  (*       (* TODO: Can this be refactored into a more general lemma? *) *)
  (*       induction Heqo. *)
  (*       - cbn in *. *)
  (*         inv H0. *)
  (*       - rewrite map_monad_unfold. *)
  (*         rewrite map_monad_unfold in H0. *)
  (*         repeat red in H0. *)
  (*         destruct H0 as (?&?&?&?&?). *)
  (*         repeat red. *)

  (*         pose proof H0. *)
  (*         eapply H in H4. *)
  (*         2: left; eauto. *)
  (*         all: eauto. *)

  (*         destruct_err_ub_oom x1; cbn in H2; inv H2. *)
  (*         { cbn in H4. *)
  (*           exists (OOM_unERR_UB_OOM oom_x). *)
  (*           eexists. *)
  (*           red in H4. *)
  (*           cbn. *)
  (*           unfold bind_ErrUbOomProp. *)
  (*           split; eauto. *)
  (*           exists (OOM_unERR_UB_OOM oom_x). *)
  (*           eexists. *)
  (*           split; cbn; eauto. *)
  (*         } *)

  (*         destruct H3 as [[] | H3]. *)
  (*         specialize (H3 x3). *)
  (*         forward H3. reflexivity. *)
  (*         cbn in H3. *)
  (*         red in H3. *)
  (*         destruct H3 as (?&?&?&?&?). *)

  (*         destruct_err_ub_oom x1; cbn in H3; rewrite <- H3 in H6; inv H6. *)
  (*         { cbn in H4. *)
  (*           exists (OOM_unERR_UB_OOM oom_x). *)
  (*           exists (fun _ => (OOM_unERR_UB_OOM oom_x)). *)
  (*           cbn. *)
  (*           unfold bind_ErrUbOomProp. *)
  (*           split. *)
  (*           - exists (success_unERR_UB_OOM (fin_to_inf_dvalue x3)). *)
  (*             exists (fun _ => (OOM_unERR_UB_OOM oom_x)). *)
  (*             split; cbn; eauto. *)
  (*             split; cbn; eauto. *)
  (*             right. *)
  (*             intros a H6. *)
  (*             exists (OOM_unERR_UB_OOM oom_x). *)
  (*             exists (fun _ => (OOM_unERR_UB_OOM oom_x)). *)
  (*             cbn. *)
  (*             split; cbn; eauto. *)
  (*             forward IHHeqo. *)
  (*             intros u H7 uv_fin H8; eapply H; eauto; right; eauto. *)
  (*             subst. *)
  (*             forward IHHeqo; eauto. *)
  (*             cbn in IHHeqo. *)
  (*             unfold bind_ErrUbOomProp in IHHeqo. *)
  (*             destruct IHHeqo as (?&?&?&?&?). *)

  (*             destruct_err_ub_oom x1; subst; cbn in H7; inv H7; auto. *)

  (*             destruct H8 as [[] | H8]. *)
  (*             specialize (H8 x6 eq_refl). *)
  (*             rewrite <- H8 in H10; inv H10. *)
  (*           - split; eauto. *)
  (*         } *)

  (*         cbn in H4. *)
  (*         destruct H5 as [[] | H5]. *)
  (*         specialize (H5 _ eq_refl). *)
  (*         rewrite <- H5 in H8. *)
  (*         inv H8. *)
  (*     } *)

  (*     { (* UB *) *)
  (*       clear H2 H3. *)
  (*       (* TODO: Can this be refactored into a more general lemma? *) *)
  (*       induction Heqo. *)
  (*       - cbn in *. *)
  (*         inv H0. *)
  (*       - rewrite map_monad_unfold. *)
  (*         rewrite map_monad_unfold in H0. *)
  (*         repeat red in H0. *)
  (*         destruct H0 as (?&?&?&?&?). *)
  (*         repeat red. *)

  (*         pose proof H0. *)
  (*         eapply H in H4. *)
  (*         2: left; eauto. *)
  (*         all: eauto. *)

  (*         destruct_err_ub_oom x1; cbn in H2; inv H2. *)
  (*         { cbn in H4. *)
  (*           exists (UB_unERR_UB_OOM ub_x). *)
  (*           eexists. *)
  (*           red in H4. *)
  (*           cbn. *)
  (*           unfold bind_ErrUbOomProp. *)
  (*           split; eauto. *)
  (*           exists (UB_unERR_UB_OOM ub_x). *)
  (*           eexists. *)
  (*           split; cbn; eauto. *)
  (*         } *)

  (*         destruct H3 as [[] | H3]. *)
  (*         specialize (H3 x3). *)
  (*         forward H3. reflexivity. *)
  (*         cbn in H3. *)
  (*         red in H3. *)
  (*         destruct H3 as (?&?&?&?&?). *)

  (*         destruct_err_ub_oom x1; cbn in H3; rewrite <- H3 in H6; inv H6. *)
  (*         { cbn in H4. *)
  (*           exists (UB_unERR_UB_OOM ub_x). *)
  (*           exists (fun _ => (UB_unERR_UB_OOM ub_x)). *)
  (*           cbn. *)
  (*           unfold bind_ErrUbOomProp. *)
  (*           split. *)
  (*           - exists (success_unERR_UB_OOM (fin_to_inf_dvalue x3)). *)
  (*             exists (fun _ => (UB_unERR_UB_OOM ub_x)). *)
  (*             split; cbn; eauto. *)
  (*             split; cbn; eauto. *)
  (*             right. *)
  (*             intros a H6. *)
  (*             exists (UB_unERR_UB_OOM ub_x). *)
  (*             exists (fun _ => (UB_unERR_UB_OOM ub_x)). *)
  (*             cbn. *)
  (*             split; cbn; eauto. *)
  (*             forward IHHeqo. *)
  (*             intros u H7 uv_fin H8; eapply H; eauto; right; eauto. *)
  (*             subst. *)
  (*             forward IHHeqo; eauto. *)
  (*             cbn in IHHeqo. *)
  (*             unfold bind_ErrUbOomProp in IHHeqo. *)
  (*             destruct IHHeqo as (?&?&?&?&?). *)

  (*             destruct_err_ub_oom x1; subst; cbn in H7; inv H7; auto. *)

  (*             destruct H8 as [[] | H8]. *)
  (*             specialize (H8 x6 eq_refl). *)
  (*             rewrite <- H8 in H10; inv H10. *)
  (*           - split; eauto. *)
  (*         } *)

  (*         cbn in H4. *)
  (*         destruct H5 as [[] | H5]. *)
  (*         specialize (H5 _ eq_refl). *)
  (*         rewrite <- H5 in H8. *)
  (*         inv H8. *)
  (*     } *)

  (*     { (* Err *) *)
  (*       clear H2 H3. *)
  (*       (* TODO: Can this be refactored into a more general lemma? *) *)
  (*       induction Heqo. *)
  (*       - cbn in *. *)
  (*         inv H0. *)
  (*       - rewrite map_monad_unfold. *)
  (*         rewrite map_monad_unfold in H0. *)
  (*         repeat red in H0. *)
  (*         destruct H0 as (?&?&?&?&?). *)
  (*         repeat red. *)

  (*         pose proof H0. *)
  (*         eapply H in H4. *)
  (*         2: left; eauto. *)
  (*         all: eauto. *)

  (*         destruct_err_ub_oom x1; cbn in H2; inv H2. *)
  (*         { cbn in H4. *)
  (*           exists (ERR_unERR_UB_OOM err_x). *)
  (*           eexists. *)
  (*           red in H4. *)
  (*           cbn. *)
  (*           unfold bind_ErrUbOomProp. *)
  (*           split; eauto. *)
  (*           exists (ERR_unERR_UB_OOM err_x). *)
  (*           eexists. *)
  (*           split; cbn; eauto. *)
  (*         } *)

  (*         destruct H3 as [[] | H3]. *)
  (*         specialize (H3 x3). *)
  (*         forward H3. reflexivity. *)
  (*         cbn in H3. *)
  (*         red in H3. *)
  (*         destruct H3 as (?&?&?&?&?). *)

  (*         destruct_err_ub_oom x1; cbn in H3; rewrite <- H3 in H6; inv H6. *)
  (*         { cbn in H4. *)
  (*           exists (ERR_unERR_UB_OOM err_x). *)
  (*           exists (fun _ => (ERR_unERR_UB_OOM err_x)). *)
  (*           cbn. *)
  (*           unfold bind_ErrUbOomProp. *)
  (*           split. *)
  (*           - exists (success_unERR_UB_OOM (fin_to_inf_dvalue x3)). *)
  (*             exists (fun _ => (ERR_unERR_UB_OOM err_x)). *)
  (*             split; cbn; eauto. *)
  (*             split; cbn; eauto. *)
  (*             right. *)
  (*             intros a H6. *)
  (*             exists (ERR_unERR_UB_OOM err_x). *)
  (*             exists (fun _ => (ERR_unERR_UB_OOM err_x)). *)
  (*             cbn. *)
  (*             split; cbn; eauto. *)
  (*             forward IHHeqo. *)
  (*             intros u H7 uv_fin H8; eapply H; eauto; right; eauto. *)
  (*             subst. *)
  (*             forward IHHeqo; eauto. *)
  (*             cbn in IHHeqo. *)
  (*             unfold bind_ErrUbOomProp in IHHeqo. *)
  (*             destruct IHHeqo as (?&?&?&?&?). *)

  (*             destruct_err_ub_oom x1; subst; cbn in H7; inv H7; auto. *)

  (*             destruct H8 as [[] | H8]. *)
  (*             specialize (H8 x6 eq_refl). *)
  (*             rewrite <- H8 in H10; inv H10. *)
  (*           - split; eauto. *)
  (*         } *)

  (*         cbn in H4. *)
  (*         destruct H5 as [[] | H5]. *)
  (*         specialize (H5 _ eq_refl). *)
  (*         rewrite <- H5 in H8. *)
  (*         inv H8. *)
  (*     } *)

  (*     destruct H2 as [[] | H2]. *)
  (*     specialize (H2 x1 eq_refl). *)
  (*     cbn in H2. *)
  (*     rewrite <- H2 in H3. *)
  (*     cbn in H3. inv H3. *)
  (*     rewrite <- H2. *)

  (*     rename H0 into MAP. *)

  (*     repeat red. *)
  (*     exists (ret (map fin_to_inf_dvalue x1)). *)
  (*     exists (fun fields => ret (IS1.LP.Events.DV.DVALUE_Struct fields)). *)
  (*     split. *)
  (*     { eapply map_monad_ErrUbOomProp_forall2. *)
  (*       apply Util.Forall2_forall. *)
  (*       split. *)
  (*       - rewrite map_length. *)

  (*         apply map_monad_ErrUbOomProp_length in MAP. *)
  (*         apply Util.Forall2_length in Heqo. *)
  (*         congruence. *)
  (*       - intros i a b NTH_fields NTH_res. *)

  (*         epose proof Util.Forall2_Nth_left NTH_fields Heqo as (x&NTHl&CONV). *)

  (*         apply Util.Nth_In in NTH_fields. *)
  (*         specialize (H a NTH_fields x CONV). *)

  (*         eapply map_monad_ErrUbOomProp_forall2 in MAP. *)
  (*         epose proof Util.Forall2_Nth_left NTHl MAP as (?&NTH_CONC&CONC). *)
  (*         specialize (H _ CONC). *)

  (*         apply Nth_map_iff in NTH_res as (?&?&?). *)
  (*         subst. *)

  (*         red in NTH_CONC, H1. *)
  (*         rewrite H1 in NTH_CONC. *)
  (*         inv NTH_CONC. *)
  (*         apply H. *)
  (*     } *)

  (*     cbn. *)
  (*     split. *)
  (*     { unfold fin_to_inf_dvalue at 2. *)
  (*       break_match_goal. *)
  (*       clear Heqs; destruct p; clear e0. *)

  (*       erewrite <- dvalue_convert_strict_struct_map; eauto. *)
  (*     } *)

  (*     right. *)
  (*     intros a H0. *)
  (*     reflexivity. *)
  (*   - (* Packed structs *) *)
  (*     red; intros dv_fin CONC_FIN. *)
  (*     red in REF. *)
  (*     cbn in REF. *)
  (*     break_match_hyp_inv. *)

  (*     unfold uvalue_concretize_fin_inf_inclusion in H. *)
  (*     apply map_monad_oom_Forall2 in Heqo. *)

  (*     red. *)
  (*     rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation. *)

  (*     red in CONC_FIN. *)
  (*     rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN. *)

  (*     repeat red in CONC_FIN. *)
  (*     destruct CONC_FIN as (?&?&?&?&?). *)

  (*     destruct_err_ub_oom x; cbn in H1; inv H1. *)
  (*     { (* OOM *) *)
  (*       clear H2 H3. *)
  (*       (* TODO: Can this be refactored into a more general lemma? *) *)
  (*       induction Heqo. *)
  (*       - cbn in *. *)
  (*         inv H0. *)
  (*       - rewrite map_monad_unfold. *)
  (*         rewrite map_monad_unfold in H0. *)
  (*         repeat red in H0. *)
  (*         destruct H0 as (?&?&?&?&?). *)
  (*         repeat red. *)

  (*         pose proof H0. *)
  (*         eapply H in H4. *)
  (*         2: left; eauto. *)
  (*         all: eauto. *)

  (*         destruct_err_ub_oom x1; cbn in H2; inv H2. *)
  (*         { cbn in H4. *)
  (*           exists (OOM_unERR_UB_OOM oom_x). *)
  (*           eexists. *)
  (*           red in H4. *)
  (*           cbn. *)
  (*           unfold bind_ErrUbOomProp. *)
  (*           split; eauto. *)
  (*           exists (OOM_unERR_UB_OOM oom_x). *)
  (*           eexists. *)
  (*           split; cbn; eauto. *)
  (*         } *)

  (*         destruct H3 as [[] | H3]. *)
  (*         specialize (H3 x3). *)
  (*         forward H3. reflexivity. *)
  (*         cbn in H3. *)
  (*         red in H3. *)
  (*         destruct H3 as (?&?&?&?&?). *)

  (*         destruct_err_ub_oom x1; cbn in H3; rewrite <- H3 in H6; inv H6. *)
  (*         { cbn in H4. *)
  (*           exists (OOM_unERR_UB_OOM oom_x). *)
  (*           exists (fun _ => (OOM_unERR_UB_OOM oom_x)). *)
  (*           cbn. *)
  (*           unfold bind_ErrUbOomProp. *)
  (*           split. *)
  (*           - exists (success_unERR_UB_OOM (fin_to_inf_dvalue x3)). *)
  (*             exists (fun _ => (OOM_unERR_UB_OOM oom_x)). *)
  (*             split; cbn; eauto. *)
  (*             split; cbn; eauto. *)
  (*             right. *)
  (*             intros a H6. *)
  (*             exists (OOM_unERR_UB_OOM oom_x). *)
  (*             exists (fun _ => (OOM_unERR_UB_OOM oom_x)). *)
  (*             cbn. *)
  (*             split; cbn; eauto. *)
  (*             forward IHHeqo. *)
  (*             intros u H7 uv_fin H8; eapply H; eauto; right; eauto. *)
  (*             subst. *)
  (*             forward IHHeqo; eauto. *)
  (*             cbn in IHHeqo. *)
  (*             unfold bind_ErrUbOomProp in IHHeqo. *)
  (*             destruct IHHeqo as (?&?&?&?&?). *)

  (*             destruct_err_ub_oom x1; subst; cbn in H7; inv H7; auto. *)

  (*             destruct H8 as [[] | H8]. *)
  (*             specialize (H8 x6 eq_refl). *)
  (*             rewrite <- H8 in H10; inv H10. *)
  (*           - split; eauto. *)
  (*         } *)

  (*         cbn in H4. *)
  (*         destruct H5 as [[] | H5]. *)
  (*         specialize (H5 _ eq_refl). *)
  (*         rewrite <- H5 in H8. *)
  (*         inv H8. *)
  (*     } *)

  (*     { (* UB *) *)
  (*       clear H2 H3. *)
  (*       (* TODO: Can this be refactored into a more general lemma? *) *)
  (*       induction Heqo. *)
  (*       - cbn in *. *)
  (*         inv H0. *)
  (*       - rewrite map_monad_unfold. *)
  (*         rewrite map_monad_unfold in H0. *)
  (*         repeat red in H0. *)
  (*         destruct H0 as (?&?&?&?&?). *)
  (*         repeat red. *)

  (*         pose proof H0. *)
  (*         eapply H in H4. *)
  (*         2: left; eauto. *)
  (*         all: eauto. *)

  (*         destruct_err_ub_oom x1; cbn in H2; inv H2. *)
  (*         { cbn in H4. *)
  (*           exists (UB_unERR_UB_OOM ub_x). *)
  (*           eexists. *)
  (*           red in H4. *)
  (*           cbn. *)
  (*           unfold bind_ErrUbOomProp. *)
  (*           split; eauto. *)
  (*           exists (UB_unERR_UB_OOM ub_x). *)
  (*           eexists. *)
  (*           split; cbn; eauto. *)
  (*         } *)

  (*         destruct H3 as [[] | H3]. *)
  (*         specialize (H3 x3). *)
  (*         forward H3. reflexivity. *)
  (*         cbn in H3. *)
  (*         red in H3. *)
  (*         destruct H3 as (?&?&?&?&?). *)

  (*         destruct_err_ub_oom x1; cbn in H3; rewrite <- H3 in H6; inv H6. *)
  (*         { cbn in H4. *)
  (*           exists (UB_unERR_UB_OOM ub_x). *)
  (*           exists (fun _ => (UB_unERR_UB_OOM ub_x)). *)
  (*           cbn. *)
  (*           unfold bind_ErrUbOomProp. *)
  (*           split. *)
  (*           - exists (success_unERR_UB_OOM (fin_to_inf_dvalue x3)). *)
  (*             exists (fun _ => (UB_unERR_UB_OOM ub_x)). *)
  (*             split; cbn; eauto. *)
  (*             split; cbn; eauto. *)
  (*             right. *)
  (*             intros a H6. *)
  (*             exists (UB_unERR_UB_OOM ub_x). *)
  (*             exists (fun _ => (UB_unERR_UB_OOM ub_x)). *)
  (*             cbn. *)
  (*             split; cbn; eauto. *)
  (*             forward IHHeqo. *)
  (*             intros u H7 uv_fin H8; eapply H; eauto; right; eauto. *)
  (*             subst. *)
  (*             forward IHHeqo; eauto. *)
  (*             cbn in IHHeqo. *)
  (*             unfold bind_ErrUbOomProp in IHHeqo. *)
  (*             destruct IHHeqo as (?&?&?&?&?). *)

  (*             destruct_err_ub_oom x1; subst; cbn in H7; inv H7; auto. *)

  (*             destruct H8 as [[] | H8]. *)
  (*             specialize (H8 x6 eq_refl). *)
  (*             rewrite <- H8 in H10; inv H10. *)
  (*           - split; eauto. *)
  (*         } *)

  (*         cbn in H4. *)
  (*         destruct H5 as [[] | H5]. *)
  (*         specialize (H5 _ eq_refl). *)
  (*         rewrite <- H5 in H8. *)
  (*         inv H8. *)
  (*     } *)

  (*     { (* Err *) *)
  (*       clear H2 H3. *)
  (*       (* TODO: Can this be refactored into a more general lemma? *) *)
  (*       induction Heqo. *)
  (*       - cbn in *. *)
  (*         inv H0. *)
  (*       - rewrite map_monad_unfold. *)
  (*         rewrite map_monad_unfold in H0. *)
  (*         repeat red in H0. *)
  (*         destruct H0 as (?&?&?&?&?). *)
  (*         repeat red. *)

  (*         pose proof H0. *)
  (*         eapply H in H4. *)
  (*         2: left; eauto. *)
  (*         all: eauto. *)

  (*         destruct_err_ub_oom x1; cbn in H2; inv H2. *)
  (*         { cbn in H4. *)
  (*           exists (ERR_unERR_UB_OOM err_x). *)
  (*           eexists. *)
  (*           red in H4. *)
  (*           cbn. *)
  (*           unfold bind_ErrUbOomProp. *)
  (*           split; eauto. *)
  (*           exists (ERR_unERR_UB_OOM err_x). *)
  (*           eexists. *)
  (*           split; cbn; eauto. *)
  (*         } *)

  (*         destruct H3 as [[] | H3]. *)
  (*         specialize (H3 x3). *)
  (*         forward H3. reflexivity. *)
  (*         cbn in H3. *)
  (*         red in H3. *)
  (*         destruct H3 as (?&?&?&?&?). *)

  (*         destruct_err_ub_oom x1; cbn in H3; rewrite <- H3 in H6; inv H6. *)
  (*         { cbn in H4. *)
  (*           exists (ERR_unERR_UB_OOM err_x). *)
  (*           exists (fun _ => (ERR_unERR_UB_OOM err_x)). *)
  (*           cbn. *)
  (*           unfold bind_ErrUbOomProp. *)
  (*           split. *)
  (*           - exists (success_unERR_UB_OOM (fin_to_inf_dvalue x3)). *)
  (*             exists (fun _ => (ERR_unERR_UB_OOM err_x)). *)
  (*             split; cbn; eauto. *)
  (*             split; cbn; eauto. *)
  (*             right. *)
  (*             intros a H6. *)
  (*             exists (ERR_unERR_UB_OOM err_x). *)
  (*             exists (fun _ => (ERR_unERR_UB_OOM err_x)). *)
  (*             cbn. *)
  (*             split; cbn; eauto. *)
  (*             forward IHHeqo. *)
  (*             intros u H7 uv_fin H8; eapply H; eauto; right; eauto. *)
  (*             subst. *)
  (*             forward IHHeqo; eauto. *)
  (*             cbn in IHHeqo. *)
  (*             unfold bind_ErrUbOomProp in IHHeqo. *)
  (*             destruct IHHeqo as (?&?&?&?&?). *)

  (*             destruct_err_ub_oom x1; subst; cbn in H7; inv H7; auto. *)

  (*             destruct H8 as [[] | H8]. *)
  (*             specialize (H8 x6 eq_refl). *)
  (*             rewrite <- H8 in H10; inv H10. *)
  (*           - split; eauto. *)
  (*         } *)

  (*         cbn in H4. *)
  (*         destruct H5 as [[] | H5]. *)
  (*         specialize (H5 _ eq_refl). *)
  (*         rewrite <- H5 in H8. *)
  (*         inv H8. *)
  (*     } *)

  (*     destruct H2 as [[] | H2]. *)
  (*     specialize (H2 x1 eq_refl). *)
  (*     cbn in H2. *)
  (*     rewrite <- H2 in H3. *)
  (*     cbn in H3. inv H3. *)
  (*     rewrite <- H2. *)

  (*     rename H0 into MAP. *)

  (*     repeat red. *)
  (*     exists (ret (map fin_to_inf_dvalue x1)). *)
  (*     exists (fun fields => ret (IS1.LP.Events.DV.DVALUE_Packed_struct fields)). *)
  (*     split. *)
  (*     { eapply map_monad_ErrUbOomProp_forall2. *)
  (*       apply Util.Forall2_forall. *)
  (*       split. *)
  (*       - rewrite map_length. *)

  (*         apply map_monad_ErrUbOomProp_length in MAP. *)
  (*         apply Util.Forall2_length in Heqo. *)
  (*         congruence. *)
  (*       - intros i a b NTH_fields NTH_res. *)

  (*         epose proof Util.Forall2_Nth_left NTH_fields Heqo as (x&NTHl&CONV). *)

  (*         apply Util.Nth_In in NTH_fields. *)
  (*         specialize (H a NTH_fields x CONV). *)

  (*         eapply map_monad_ErrUbOomProp_forall2 in MAP. *)
  (*         epose proof Util.Forall2_Nth_left NTHl MAP as (?&NTH_CONC&CONC). *)
  (*         specialize (H _ CONC). *)

  (*         apply Nth_map_iff in NTH_res as (?&?&?). *)
  (*         subst. *)

  (*         red in NTH_CONC, H1. *)
  (*         rewrite H1 in NTH_CONC. *)
  (*         inv NTH_CONC. *)
  (*         apply H. *)
  (*     } *)

  (*     cbn. *)
  (*     split. *)
  (*     { unfold fin_to_inf_dvalue at 2. *)
  (*       break_match_goal. *)
  (*       clear Heqs; destruct p; clear e0. *)

  (*       erewrite <- dvalue_convert_strict_packed_struct_map; eauto. *)
  (*     } *)

  (*     right. *)
  (*     intros a H0. *)
  (*     reflexivity. *)
  (*   - (* Array *) *)
  (*     red; intros dv_fin CONC_FIN. *)
  (*     red in REF. *)
  (*     cbn in REF. *)
  (*     break_match_hyp_inv. *)

  (*     unfold uvalue_concretize_u_fin_inf_inclusion in H. *)
  (*     apply map_monad_oom_Forall2 in Heqo. *)

  (*     red. *)
  (*     rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation. *)

  (*     red in CONC_FIN. *)
  (*     rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN. *)

  (*     revert dv_fin CONC_FIN. *)

  (*     induction Heqo; intros dv_fin CONC_FIN; *)
  (*       repeat red in CONC_FIN; *)
  (*       destruct CONC_FIN as (?&?&?&?&?).       *)
  (*     + cbn in H0. *)
  (*       inv H0. *)
  (*       destruct H2 as [[] | H2]. *)

  (*       specialize (H2 _ eq_refl). *)
  (*       cbn in H2. *)

  (*       repeat red. *)
  (*       exists (success_unERR_UB_OOM []). *)
  (*       exists (fun _ => success_unERR_UB_OOM (fin_to_inf_dvalue (DVALUE_Array []))). *)
  (*       split; cbn; eauto. *)
  (*       rewrite <- H2. *)
  (*       cbn. *)
  (*       split; eauto. *)
  (*       right. *)
  (*       intros; subst. *)
  (*       rewrite fin_to_inf_dvalue_array. *)
  (*       cbn. *)
  (*       auto. *)
  (*     + forward IHHeqo. *)
  (*       { intros e H4 uv_fin H5 res H6. *)
  (*         eapply H. *)
  (*         right; auto. *)
  (*         apply H5. *)
  (*         auto. *)
  (*       } *)

  (*       rewrite map_monad_unfold in H1. *)
  (*       repeat red in H1. *)
  (*       destruct H1 as (?&?&?&?&?). *)
  (*       subst. *)

  (*       pose proof (H x (or_introl eq_refl) _ H0 _ H1). *)
  (*       destruct_err_ub_oom x2; subst. *)

  (*       { (* OOM *) *)
  (*         clear H5 H3. *)
  (*         exists (OOM_unERR_UB_OOM oom_x). *)
  (*         eexists. *)
  (*         split; cbn; eauto. *)

  (*         red. *)
  (*         exists (fmap fin_to_inf_dvalue (OOM_unERR_UB_OOM oom_x)). *)
  (*         eexists. *)
  (*         split; cbn; eauto. *)
  (*       } *)

  (*       { (* UB *) *)
  (*         clear H5 H3. *)
  (*         exists (UB_unERR_UB_OOM ub_x). *)
  (*         eexists. *)
  (*         split; cbn; eauto. *)

  (*         red. *)
  (*         exists (fmap fin_to_inf_dvalue (UB_unERR_UB_OOM ub_x)). *)
  (*         eexists. *)
  (*         split; cbn; eauto. *)
  (*       } *)

  (*       { (* Err *) *)
  (*         clear H5 H3. *)
  (*         exists (ERR_unERR_UB_OOM err_x). *)
  (*         eexists. *)
  (*         split; cbn; eauto. *)

  (*         red. *)
  (*         exists (fmap fin_to_inf_dvalue (ERR_unERR_UB_OOM err_x)). *)
  (*         eexists. *)
  (*         split; cbn; eauto. *)
  (*       } *)

  (*       destruct H5 as [[] | H5]. *)
  (*       specialize (H5 _ eq_refl). *)
  (*       repeat red in H5. *)
  (*       destruct H5 as (?&?&?&?&?). *)

  (*       destruct_err_ub_oom x2; cbn in H5, H3; rewrite <- H5 in H3; cbn in H3; subst. *)
  (*       { (* OOM *) *)
  (*         clear H3 H6. *)
  (*         cbn; setoid_rewrite <- H5. *)
  (*         exists (OOM_unERR_UB_OOM oom_x). *)
  (*         eexists. *)
  (*         split; cbn; eauto. *)

  (*         red. *)
  (*         exists (fmap fin_to_inf_dvalue (success_unERR_UB_OOM x0)). *)
  (*         exists (fun _ => OOM_unERR_UB_OOM oom_x). *)
  (*         split; cbn; eauto. *)
  (*         split; cbn; eauto. *)
  (*         right. *)
  (*         intros; subst. *)
  (*         red. *)

  (*         exists (OOM_unERR_UB_OOM oom_x). *)
  (*         eexists. *)
  (*         split; cbn; eauto. *)

  (*         specialize (IHHeqo (OOM_unERR_UB_OOM oom_x)). *)
  (*         forward IHHeqo. *)
  (*         { cbn. *)
  (*           red. *)
  (*           exists (OOM_unERR_UB_OOM oom_x). *)
  (*           eexists. *)
  (*           split; cbn; eauto. *)
  (*         } *)

  (*         repeat red in IHHeqo. *)
  (*         destruct IHHeqo as (?&?&?&?&?). *)
  (*         destruct_err_ub_oom x2; cbn in H6; inv H6; eauto. *)

  (*         destruct H7 as [[] | H7]. *)
  (*         specialize (H7 _ eq_refl). *)
  (*         cbn in H7. *)
  (*         rewrite <- H7 in H9. *)
  (*         cbn in H9. *)
  (*         inv H9. *)
  (*       } *)

  (*       { (* UB *) *)
  (*         clear H3 H6. *)
  (*         cbn; setoid_rewrite <- H5. *)
  (*         exists (UB_unERR_UB_OOM ub_x). *)
  (*         eexists. *)
  (*         split; cbn; eauto. *)

  (*         red. *)
  (*         exists (fmap fin_to_inf_dvalue (success_unERR_UB_OOM x0)). *)
  (*         exists (fun _ => UB_unERR_UB_OOM ub_x). *)
  (*         split; cbn; eauto. *)
  (*         split; cbn; eauto. *)
  (*         right. *)
  (*         intros; subst. *)
  (*         red. *)

  (*         exists (UB_unERR_UB_OOM ub_x). *)
  (*         eexists. *)
  (*         split; cbn; eauto. *)

  (*         specialize (IHHeqo (UB_unERR_UB_OOM ub_x)). *)
  (*         forward IHHeqo. *)
  (*         { cbn. *)
  (*           red. *)
  (*           exists (UB_unERR_UB_OOM ub_x). *)
  (*           eexists. *)
  (*           split; cbn; eauto. *)
  (*         } *)

  (*         repeat red in IHHeqo. *)
  (*         destruct IHHeqo as (?&?&?&?&?). *)
  (*         destruct_err_ub_oom x2; cbn in H6; inv H6; eauto. *)

  (*         destruct H7 as [[] | H7]. *)
  (*         specialize (H7 _ eq_refl). *)
  (*         cbn in H7. *)
  (*         rewrite <- H7 in H9. *)
  (*         cbn in H9. *)
  (*         inv H9. *)
  (*       } *)

  (*       { (* Err *) *)
  (*         clear H3 H6. *)
  (*         cbn; setoid_rewrite <- H5. *)
  (*         exists (ERR_unERR_UB_OOM err_x). *)
  (*         eexists. *)
  (*         split; cbn; eauto. *)

  (*         red. *)
  (*         exists (fmap fin_to_inf_dvalue (success_unERR_UB_OOM x0)). *)
  (*         exists (fun _ => ERR_unERR_UB_OOM err_x). *)
  (*         split; cbn; eauto. *)
  (*         split; cbn; eauto. *)
  (*         right. *)
  (*         intros; subst. *)
  (*         red. *)

  (*         exists (ERR_unERR_UB_OOM err_x). *)
  (*         eexists. *)
  (*         split; cbn; eauto. *)

  (*         specialize (IHHeqo (ERR_unERR_UB_OOM err_x)). *)
  (*         forward IHHeqo. *)
  (*         { cbn. *)
  (*           red. *)
  (*           exists (ERR_unERR_UB_OOM err_x). *)
  (*           eexists. *)
  (*           split; cbn; eauto. *)
  (*         } *)

  (*         repeat red in IHHeqo. *)
  (*         destruct IHHeqo as (?&?&?&?&?). *)
  (*         destruct_err_ub_oom x2; cbn in H6; inv H6; eauto. *)

  (*         destruct H7 as [[] | H7]. *)
  (*         specialize (H7 _ eq_refl). *)
  (*         cbn in H7. *)
  (*         rewrite <- H7 in H9. *)
  (*         cbn in H9. *)
  (*         inv H9. *)
  (*       } *)

  (*       destruct H6 as [[] | H6]. *)
  (*       specialize (H6 _ eq_refl). *)
  (*       cbn in H6. *)
  (*       rewrite <- H6 in H3. *)
  (*       cbn in H3. *)
  (*       destruct H3 as [[] | H3]. *)
  (*       specialize (H3 _ eq_refl). *)

  (*       specialize (IHHeqo (success_unERR_UB_OOM (DVALUE_Array x5))). *)
  (*       forward IHHeqo. *)
  (*       { cbn. *)
  (*         red. *)
  (*         exists (success_unERR_UB_OOM x5). *)
  (*         exists (fun xs => ret (DVALUE_Array xs)). *)
  (*         split; cbn; eauto. *)
  (*       } *)

  (*       repeat red in IHHeqo. *)
  (*       destruct IHHeqo as (?&?&?&?&?). *)
  (*       destruct_err_ub_oom x2; cbn in H8; inv H8. *)
  (*       destruct H9 as [[] | H9]. *)
  (*       specialize (H9 _ eq_refl). *)
  (*       cbn in H9. *)
  (*       rewrite <- H9 in H11. *)
  (*       inv H11. *)
  (*       rewrite <- H6 in H5. *)
  (*       inv H5. *)

  (*       repeat red. *)
  (*       exists (ret (fmap fin_to_inf_dvalue (x0::x5))). *)
  (*       exists (fun xs => ret (IS1.LP.Events.DV.DVALUE_Array xs)). *)
  (*       rewrite map_monad_unfold. *)
  (*       split; cbn; eauto. *)
  (*       2: { *)
  (*         rewrite <- H11; cbn. *)
  (*         rewrite <- H3; cbn. *)
  (*         split; cbn; eauto. *)
  (*         rewrite fin_to_inf_dvalue_array. *)
  (*         cbn. *)
  (*         reflexivity. *)
  (*       } *)

  (*       exists (fmap fin_to_inf_dvalue (success_unERR_UB_OOM x0)). *)
  (*       exists (fun _ => ret (fmap fin_to_inf_dvalue (x0 :: x5))). *)
  (*       split; cbn; eauto. *)
  (*       split; cbn; eauto. *)
  (*       right. *)
  (*       intros; subst. *)
  (*       red. *)

  (*       exists (success_unERR_UB_OOM x7). *)
  (*       exists (fun _ => ret (fmap fin_to_inf_dvalue (x0 :: x5))). *)
  (*       split; cbn; eauto. *)
  (*       split; cbn; eauto. *)
  (*       right. *)
  (*       intros; subst. *)
  (*       rewrite fin_to_inf_dvalue_array in H10. *)
  (*       inv H10. *)
  (*       { (* TODO: should probably make this a lemma... *) *)
  (*         induction x5; eauto. *)
  (*       } *)
  (*   - (* Vector *) *)
  (*     red; intros dv_fin CONC_FIN. *)
  (*     red in REF. *)
  (*     cbn in REF. *)
  (*     break_match_hyp_inv. *)

  (*     unfold uvalue_concretize_u_fin_inf_inclusion in H. *)
  (*     apply map_monad_oom_Forall2 in Heqo. *)

  (*     red. *)
  (*     rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation. *)

  (*     red in CONC_FIN. *)
  (*     rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN. *)

  (*     revert dv_fin CONC_FIN. *)

  (*     induction Heqo; intros dv_fin CONC_FIN; *)
  (*       repeat red in CONC_FIN; *)
  (*       destruct CONC_FIN as (?&?&?&?&?).       *)
  (*     + cbn in H0. *)
  (*       inv H0. *)
  (*       destruct H2 as [[] | H2]. *)

  (*       specialize (H2 _ eq_refl). *)
  (*       cbn in H2. *)

  (*       repeat red. *)
  (*       exists (success_unERR_UB_OOM []). *)
  (*       exists (fun _ => success_unERR_UB_OOM (fin_to_inf_dvalue (DVALUE_Vector []))). *)
  (*       split; cbn; eauto. *)
  (*       rewrite <- H2. *)
  (*       cbn. *)
  (*       split; eauto. *)
  (*       right. *)
  (*       intros; subst. *)
  (*       rewrite fin_to_inf_dvalue_vector. *)
  (*       cbn. *)
  (*       auto. *)
  (*     + forward IHHeqo. *)
  (*       { intros e H4 uv_fin H5 res H6. *)
  (*         eapply H. *)
  (*         right; auto. *)
  (*         apply H5. *)
  (*         auto. *)
  (*       } *)

  (*       rewrite map_monad_unfold in H1. *)
  (*       repeat red in H1. *)
  (*       destruct H1 as (?&?&?&?&?). *)
  (*       subst. *)

  (*       pose proof (H x (or_introl eq_refl) _ H0 _ H1). *)
  (*       destruct_err_ub_oom x2; subst. *)

  (*       { (* OOM *) *)
  (*         clear H5 H3. *)
  (*         exists (OOM_unERR_UB_OOM oom_x). *)
  (*         eexists. *)
  (*         split; cbn; eauto. *)

  (*         red. *)
  (*         exists (fmap fin_to_inf_dvalue (OOM_unERR_UB_OOM oom_x)). *)
  (*         eexists. *)
  (*         split; cbn; eauto. *)
  (*       } *)

  (*       { (* UB *) *)
  (*         clear H5 H3. *)
  (*         exists (UB_unERR_UB_OOM ub_x). *)
  (*         eexists. *)
  (*         split; cbn; eauto. *)

  (*         red. *)
  (*         exists (fmap fin_to_inf_dvalue (UB_unERR_UB_OOM ub_x)). *)
  (*         eexists. *)
  (*         split; cbn; eauto. *)
  (*       } *)

  (*       { (* Err *) *)
  (*         clear H5 H3. *)
  (*         exists (ERR_unERR_UB_OOM err_x). *)
  (*         eexists. *)
  (*         split; cbn; eauto. *)

  (*         red. *)
  (*         exists (fmap fin_to_inf_dvalue (ERR_unERR_UB_OOM err_x)). *)
  (*         eexists. *)
  (*         split; cbn; eauto. *)
  (*       } *)

  (*       destruct H5 as [[] | H5]. *)
  (*       specialize (H5 _ eq_refl). *)
  (*       repeat red in H5. *)
  (*       destruct H5 as (?&?&?&?&?). *)

  (*       destruct_err_ub_oom x2; cbn in H5, H3; rewrite <- H5 in H3; cbn in H3; subst. *)
  (*       { (* OOM *) *)
  (*         clear H3 H6. *)
  (*         cbn; setoid_rewrite <- H5. *)
  (*         exists (OOM_unERR_UB_OOM oom_x). *)
  (*         eexists. *)
  (*         split; cbn; eauto. *)

  (*         red. *)
  (*         exists (fmap fin_to_inf_dvalue (success_unERR_UB_OOM x0)). *)
  (*         exists (fun _ => OOM_unERR_UB_OOM oom_x). *)
  (*         split; cbn; eauto. *)
  (*         split; cbn; eauto. *)
  (*         right. *)
  (*         intros; subst. *)
  (*         red. *)

  (*         exists (OOM_unERR_UB_OOM oom_x). *)
  (*         eexists. *)
  (*         split; cbn; eauto. *)

  (*         specialize (IHHeqo (OOM_unERR_UB_OOM oom_x)). *)
  (*         forward IHHeqo. *)
  (*         { cbn. *)
  (*           red. *)
  (*           exists (OOM_unERR_UB_OOM oom_x). *)
  (*           eexists. *)
  (*           split; cbn; eauto. *)
  (*         } *)

  (*         repeat red in IHHeqo. *)
  (*         destruct IHHeqo as (?&?&?&?&?). *)
  (*         destruct_err_ub_oom x2; cbn in H6; inv H6; eauto. *)

  (*         destruct H7 as [[] | H7]. *)
  (*         specialize (H7 _ eq_refl). *)
  (*         cbn in H7. *)
  (*         rewrite <- H7 in H9. *)
  (*         cbn in H9. *)
  (*         inv H9. *)
  (*       } *)

  (*       { (* UB *) *)
  (*         clear H3 H6. *)
  (*         cbn; setoid_rewrite <- H5. *)
  (*         exists (UB_unERR_UB_OOM ub_x). *)
  (*         eexists. *)
  (*         split; cbn; eauto. *)

  (*         red. *)
  (*         exists (fmap fin_to_inf_dvalue (success_unERR_UB_OOM x0)). *)
  (*         exists (fun _ => UB_unERR_UB_OOM ub_x). *)
  (*         split; cbn; eauto. *)
  (*         split; cbn; eauto. *)
  (*         right. *)
  (*         intros; subst. *)
  (*         red. *)

  (*         exists (UB_unERR_UB_OOM ub_x). *)
  (*         eexists. *)
  (*         split; cbn; eauto. *)

  (*         specialize (IHHeqo (UB_unERR_UB_OOM ub_x)). *)
  (*         forward IHHeqo. *)
  (*         { cbn. *)
  (*           red. *)
  (*           exists (UB_unERR_UB_OOM ub_x). *)
  (*           eexists. *)
  (*           split; cbn; eauto. *)
  (*         } *)

  (*         repeat red in IHHeqo. *)
  (*         destruct IHHeqo as (?&?&?&?&?). *)
  (*         destruct_err_ub_oom x2; cbn in H6; inv H6; eauto. *)

  (*         destruct H7 as [[] | H7]. *)
  (*         specialize (H7 _ eq_refl). *)
  (*         cbn in H7. *)
  (*         rewrite <- H7 in H9. *)
  (*         cbn in H9. *)
  (*         inv H9. *)
  (*       } *)

  (*       { (* Err *) *)
  (*         clear H3 H6. *)
  (*         cbn; setoid_rewrite <- H5. *)
  (*         exists (ERR_unERR_UB_OOM err_x). *)
  (*         eexists. *)
  (*         split; cbn; eauto. *)

  (*         red. *)
  (*         exists (fmap fin_to_inf_dvalue (success_unERR_UB_OOM x0)). *)
  (*         exists (fun _ => ERR_unERR_UB_OOM err_x). *)
  (*         split; cbn; eauto. *)
  (*         split; cbn; eauto. *)
  (*         right. *)
  (*         intros; subst. *)
  (*         red. *)

  (*         exists (ERR_unERR_UB_OOM err_x). *)
  (*         eexists. *)
  (*         split; cbn; eauto. *)

  (*         specialize (IHHeqo (ERR_unERR_UB_OOM err_x)). *)
  (*         forward IHHeqo. *)
  (*         { cbn. *)
  (*           red. *)
  (*           exists (ERR_unERR_UB_OOM err_x). *)
  (*           eexists. *)
  (*           split; cbn; eauto. *)
  (*         } *)

  (*         repeat red in IHHeqo. *)
  (*         destruct IHHeqo as (?&?&?&?&?). *)
  (*         destruct_err_ub_oom x2; cbn in H6; inv H6; eauto. *)

  (*         destruct H7 as [[] | H7]. *)
  (*         specialize (H7 _ eq_refl). *)
  (*         cbn in H7. *)
  (*         rewrite <- H7 in H9. *)
  (*         cbn in H9. *)
  (*         inv H9. *)
  (*       } *)

  (*       destruct H6 as [[] | H6]. *)
  (*       specialize (H6 _ eq_refl). *)
  (*       cbn in H6. *)
  (*       rewrite <- H6 in H3. *)
  (*       cbn in H3. *)
  (*       destruct H3 as [[] | H3]. *)
  (*       specialize (H3 _ eq_refl). *)

  (*       specialize (IHHeqo (success_unERR_UB_OOM (DVALUE_Vector x5))). *)
  (*       forward IHHeqo. *)
  (*       { cbn. *)
  (*         red. *)
  (*         exists (success_unERR_UB_OOM x5). *)
  (*         exists (fun xs => ret (DVALUE_Vector xs)). *)
  (*         split; cbn; eauto. *)
  (*       } *)

  (*       repeat red in IHHeqo. *)
  (*       destruct IHHeqo as (?&?&?&?&?). *)
  (*       destruct_err_ub_oom x2; cbn in H8; inv H8. *)
  (*       destruct H9 as [[] | H9]. *)
  (*       specialize (H9 _ eq_refl). *)
  (*       cbn in H9. *)
  (*       rewrite <- H9 in H11. *)
  (*       inv H11. *)
  (*       rewrite <- H6 in H5. *)
  (*       inv H5. *)

  (*       repeat red. *)
  (*       exists (ret (fmap fin_to_inf_dvalue (x0::x5))). *)
  (*       exists (fun xs => ret (IS1.LP.Events.DV.DVALUE_Vector xs)). *)
  (*       rewrite map_monad_unfold. *)
  (*       split; cbn; eauto. *)
  (*       2: { *)
  (*         rewrite <- H11; cbn. *)
  (*         rewrite <- H3; cbn. *)
  (*         split; cbn; eauto. *)
  (*         rewrite fin_to_inf_dvalue_vector. *)
  (*         cbn. *)
  (*         reflexivity. *)
  (*       } *)

  (*       exists (fmap fin_to_inf_dvalue (success_unERR_UB_OOM x0)). *)
  (*       exists (fun _ => ret (fmap fin_to_inf_dvalue (x0 :: x5))). *)
  (*       split; cbn; eauto. *)
  (*       split; cbn; eauto. *)
  (*       right. *)
  (*       intros; subst. *)
  (*       red. *)

  (*       exists (success_unERR_UB_OOM x7). *)
  (*       exists (fun _ => ret (fmap fin_to_inf_dvalue (x0 :: x5))). *)
  (*       split; cbn; eauto. *)
  (*       split; cbn; eauto. *)
  (*       right. *)
  (*       intros; subst. *)
  (*       rewrite fin_to_inf_dvalue_vector in H10. *)
  (*       inv H10. *)
  (*       { (* TODO: should probably make this a lemma... *) *)
  (*         induction x5; eauto. *)
  (*       } *)
  (*   - (* IBinop *) *)
  (*     red; intros dv_fin CONC_FIN. *)
  (*     red in REF. *)
  (*     cbn in REF. *)
  (*     break_match_hyp_inv. *)
  (*     break_match_hyp_inv. *)

  (*     unfold uvalue_concretize_u_fin_inf_inclusion in IHuv_inf1, IHuv_inf2. *)

  (*     specialize (IHuv_inf1 u Heqo). *)
  (*     specialize (IHuv_inf2 u0 Heqo0). *)

  (*     red. *)
  (*     rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation. *)

  (*     red in CONC_FIN. *)
  (*     rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN. *)

  (*     repeat red in CONC_FIN. *)
  (*     destruct CONC_FIN as (?&?&?&?&?). *)

  (*     specialize (IHuv_inf1 _ H). *)
  (*     destruct_err_ub_oom x; cbn in H0; inv H0. *)

  (*     { (* OOM *) *)
  (*       exists (OOM_unERR_UB_OOM oom_x). *)
  (*       eexists. *)
  (*       split; cbn; eauto. *)
  (*     } *)

  (*     { (* UB *) *)
  (*       exists (UB_unERR_UB_OOM ub_x). *)
  (*       eexists. *)
  (*       split; cbn; eauto. *)
  (*     } *)

  (*     { (* Err *) *)
  (*       exists (ERR_unERR_UB_OOM err_x). *)
  (*       eexists. *)
  (*       split; cbn; eauto. *)
  (*     } *)

  (*     destruct H1 as [[] | H1]. *)
  (*     specialize (H1 _ eq_refl). *)
  (*     cbn in H1. *)
  (*     repeat red in H1. *)
  (*     destruct H1 as (?&?&?&?&?). *)

  (*     specialize (IHuv_inf2 _ H0). *)

  (*     repeat red. *)
  (*     exists (fmap fin_to_inf_dvalue (success_unERR_UB_OOM x1)). *)
  (*     exists (fun _ => fmap fin_to_inf_dvalue (x0 x1)). *)
  (*     split; cbn; eauto. *)
  (*     split; cbn; eauto. *)
  (*     right. *)
  (*     intros; subst. *)
  (*     red. *)

  (*     exists (fmap fin_to_inf_dvalue x). *)
  (*     eexists. *)

  (*     destruct_err_ub_oom x; cbn in H1; rewrite <- H1 in H2; inv H2; *)
  (*       rewrite <- H1; *)
  (*       cbn; *)
  (*       split; cbn; eauto. *)

  (*     destruct H3 as [[] | H3]. *)
  (*     specialize (H3 _ eq_refl). *)
  (*     rewrite <- H3 in H1. *)

  (*     remember (eval_iop iop x1 x3) as x1x3. *)
  (*     destruct_err_ub_oom x1x3; inv H1; *)
  (*     rewrite <- H3; cbn. *)
  (*     cbn in H1. *)

  (*     apply IHuv_inf1 in H. *)
  (*     apply IHuv_inf2 in H0. *)

  (*     repeat red. *)
  (*     exists (ret (fin_to_inf_dvalue x1)). *)
  (*     exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))). *)
  (*     cbn. *)
  (*     rewrite <- H1. *)
  (*     cbn. *)
  (*     split; eauto. *)
  (*     split; eauto. *)

  (*     right. *)
  (*     intros a H3. *)
  (*     repeat red. *)
  (*     exists (ret (fin_to_inf_dvalue x3)). *)
  (*     exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 x3))). *)
  (*     cbn. *)
  (*     rewrite <- H2. *)
  (*     cbn. *)
  (*     split; eauto. *)
  (*     split; eauto. *)

  (*     right. *)
  (*     intros a0 H4. *)

  (*     eapply eval_iop_fin_inf; eauto. *)
  (*   - (* ICmp *) *)
  (*     red; intros dv_fin CONC_FIN. *)
  (*     red in REF. *)
  (*     cbn in REF. *)
  (*     break_match_hyp_inv. *)
  (*     break_match_hyp_inv. *)

  (*     unfold uvalue_concretize_fin_inf_inclusion in IHuv_inf1, IHuv_inf2. *)

  (*     specialize (IHuv_inf1 u Heqo). *)
  (*     specialize (IHuv_inf2 u0 Heqo0). *)

  (*     rewrite IS1.MEM.CP.CONC.concretize_equation. *)
  (*     red. *)
  (*     rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation. *)

  (*     rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN. *)
  (*     red in CONC_FIN. *)
  (*     rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN. *)

  (*     repeat red in CONC_FIN. *)
  (*     destruct CONC_FIN as (?&?&?&?&?). *)
  (*     destruct_err_ub_oom x; cbn in H0; inv H0. *)
  (*     destruct H1 as [[] | H1]. *)
  (*     specialize (H1 _ eq_refl). *)
  (*     cbn in H1. *)
  (*     repeat red in H1. *)
  (*     destruct H1 as (?&?&?&?&?). *)
  (*     destruct_err_ub_oom x; cbn in H1; rewrite <- H1 in H3; inv H3. *)
  (*     destruct H2 as [[] | H2]. *)
  (*     specialize (H2 _ eq_refl). *)
  (*     rewrite <- H2 in H5, H1. *)

  (*     remember (eval_icmp cmp0 x1 x3) as x1x3. *)
  (*     destruct_err_ub_oom x1x3; inv H5. *)
  (*     cbn in H1. *)

  (*     apply IHuv_inf1 in H. *)
  (*     apply IHuv_inf2 in H0. *)

  (*     repeat red. *)
  (*     exists (ret (fin_to_inf_dvalue x1)). *)
  (*     exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))). *)
  (*     cbn. *)
  (*     rewrite <- H1. *)
  (*     cbn. *)
  (*     split; eauto. *)
  (*     split; eauto. *)

  (*     right. *)
  (*     intros a H3. *)
  (*     repeat red. *)
  (*     exists (ret (fin_to_inf_dvalue x3)). *)
  (*     exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 x3))). *)
  (*     cbn. *)
  (*     rewrite <- H2. *)
  (*     cbn. *)
  (*     split; eauto. *)
  (*     split; eauto. *)

  (*     right. *)
  (*     intros a0 H4. *)

  (*     eapply eval_icmp_fin_inf; eauto. *)
  (*   - (* FBinop *) *)
  (*     red; intros dv_fin CONC_FIN. *)
  (*     red in REF. *)
  (*     cbn in REF. *)
  (*     break_match_hyp_inv. *)
  (*     break_match_hyp_inv. *)

  (*     unfold uvalue_concretize_fin_inf_inclusion in IHuv_inf1, IHuv_inf2. *)

  (*     specialize (IHuv_inf1 u Heqo). *)
  (*     specialize (IHuv_inf2 u0 Heqo0). *)

  (*     rewrite IS1.MEM.CP.CONC.concretize_equation. *)
  (*     red. *)
  (*     rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation. *)

  (*     rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN. *)
  (*     red in CONC_FIN. *)
  (*     rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN. *)

  (*     repeat red in CONC_FIN. *)
  (*     destruct CONC_FIN as (?&?&?&?&?). *)
  (*     destruct_err_ub_oom x; cbn in H0; inv H0. *)
  (*     destruct H1 as [[] | H1]. *)
  (*     specialize (H1 _ eq_refl). *)
  (*     cbn in H1. *)
  (*     repeat red in H1. *)
  (*     destruct H1 as (?&?&?&?&?). *)
  (*     destruct_err_ub_oom x; cbn in H1; rewrite <- H1 in H3; inv H3. *)
  (*     destruct H2 as [[] | H2]. *)
  (*     specialize (H2 _ eq_refl). *)
  (*     rewrite <- H2 in H5, H1. *)

  (*     remember (eval_fop fop x1 x3) as x1x3. *)
  (*     destruct_err_ub_oom x1x3; inv H5. *)
  (*     cbn in H1. *)

  (*     apply IHuv_inf1 in H. *)
  (*     apply IHuv_inf2 in H0. *)

  (*     repeat red. *)
  (*     exists (ret (fin_to_inf_dvalue x1)). *)
  (*     exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))). *)
  (*     cbn. *)
  (*     rewrite <- H1. *)
  (*     cbn. *)
  (*     split; eauto. *)
  (*     split; eauto. *)

  (*     right. *)
  (*     intros a H3. *)
  (*     repeat red. *)
  (*     exists (ret (fin_to_inf_dvalue x3)). *)
  (*     exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 x3))). *)
  (*     cbn. *)
  (*     rewrite <- H2. *)
  (*     cbn. *)
  (*     split; eauto. *)
  (*     split; eauto. *)

  (*     right. *)
  (*     intros a0 H4. *)

  (*     eapply eval_fop_fin_inf; eauto. *)
  (*   - (* fcmp *) *)
  (*     red; intros dv_fin CONC_FIN. *)
  (*     red in REF. *)
  (*     cbn in REF. *)
  (*     break_match_hyp_inv. *)
  (*     break_match_hyp_inv. *)

  (*     unfold uvalue_concretize_fin_inf_inclusion in IHuv_inf1, IHuv_inf2. *)

  (*     specialize (IHuv_inf1 u Heqo). *)
  (*     specialize (IHuv_inf2 u0 Heqo0). *)

  (*     rewrite IS1.MEM.CP.CONC.concretize_equation. *)
  (*     red. *)
  (*     rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation. *)

  (*     rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN. *)
  (*     red in CONC_FIN. *)
  (*     rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN. *)

  (*     repeat red in CONC_FIN. *)
  (*     destruct CONC_FIN as (?&?&?&?&?). *)
  (*     destruct_err_ub_oom x; cbn in H0; inv H0. *)
  (*     destruct H1 as [[] | H1]. *)
  (*     specialize (H1 _ eq_refl). *)
  (*     cbn in H1. *)
  (*     repeat red in H1. *)
  (*     destruct H1 as (?&?&?&?&?). *)
  (*     destruct_err_ub_oom x; cbn in H1; rewrite <- H1 in H3; inv H3. *)
  (*     destruct H2 as [[] | H2]. *)
  (*     specialize (H2 _ eq_refl). *)
  (*     rewrite <- H2 in H5, H1. *)

  (*     remember (eval_fcmp cmp0 x1 x3) as x1x3. *)
  (*     destruct_err_ub_oom x1x3; inv H5. *)
  (*     cbn in H1. *)

  (*     apply IHuv_inf1 in H. *)
  (*     apply IHuv_inf2 in H0. *)

  (*     repeat red. *)
  (*     exists (ret (fin_to_inf_dvalue x1)). *)
  (*     exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))). *)
  (*     cbn. *)
  (*     rewrite <- H1. *)
  (*     cbn. *)
  (*     split; eauto. *)
  (*     split; eauto. *)

  (*     right. *)
  (*     intros a H3. *)
  (*     repeat red. *)
  (*     exists (ret (fin_to_inf_dvalue x3)). *)
  (*     exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 x3))). *)
  (*     cbn. *)
  (*     rewrite <- H2. *)
  (*     cbn. *)
  (*     split; eauto. *)
  (*     split; eauto. *)

  (*     right. *)
  (*     intros a0 H4. *)

  (*     eapply eval_fcmp_fin_inf; eauto. *)
  (*   - (* Conversion *) *)
  (*     red; intros dv_fin CONC_FIN. *)
  (*     red in REF. *)
  (*     cbn in REF. *)
  (*     break_match_hyp_inv. *)

  (*     specialize (IHuv_inf _ Heqo). *)
  (*     unfold uvalue_concretize_fin_inf_inclusion in IHuv_inf. *)

  (*     rewrite IS1.MEM.CP.CONC.concretize_equation. *)
  (*     red. *)
  (*     rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation. *)

  (*     rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN. *)
  (*     red in CONC_FIN. *)
  (*     rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN. *)

  (*     repeat red in CONC_FIN. *)
  (*     destruct CONC_FIN as (?&?&?&?&?). *)
  (*     destruct_err_ub_oom x; cbn in H0; inv H0. *)
  (*     destruct H1 as [[] | H1]. *)
  (*     specialize (H1 _ eq_refl). *)
  (*     cbn in H1. *)

  (*     specialize (IHuv_inf _ H). *)
  (*     repeat red. *)
  (*     exists (ret (fin_to_inf_dvalue x1)). *)
  (*     exists (fun _ => (fmap fin_to_inf_dvalue (x0 x1))). *)
  (*     cbn; rewrite H3; cbn. *)
  (*     split; eauto. *)
  (*     split; eauto. *)

  (*     right; intros ? ?; subst. *)
  (*     break_match_hyp. *)
  (*     { (* Conv_Pure *) *)
  (*       pose proof get_conv_case_pure_fin_inf _ _ _ _ _ Heqc as CONV. *)
  (*       rewrite CONV. *)
  (*       rewrite <- H1 in H3; inv H3; auto. *)
  (*     } *)

  (*     { (* Conv_ItoP *) *)
  (*       break_match_hyp; *)
  (*         rewrite <- H1 in H3; inv H3. *)

  (*       pose proof get_conv_case_itop_fin_inf _ _ _ _ _ Heqc as CONV. *)
  (*       rewrite CONV. *)
  (*       admit. *)
  (*     } *)

  (*     { (* Conv_PtoI *) *)
  (*       admit. *)
  (*     } *)

  (*     { (* Conv_Illegal *) *)
  (*       exfalso. *)
  (*       rewrite <- H1 in H3; inv H3. *)
  (*     } *)
  (*   - (* GetElementPtr *) *)
  (*     red; intros dv_fin CONC_FIN. *)
  (*     red in REF. *)
  (*     cbn in REF. *)
  (*     break_match_hyp_inv. *)
  (*     break_match_hyp_inv. *)

  (*     pose proof (IHuv_inf u Heqo) as IHuv_inf_u. *)
  (*     unfold uvalue_concretize_fin_inf_inclusion in IHuv_inf_u. *)

  (*     rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN. *)
  (*     red in CONC_FIN. *)
  (*     rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN. *)

  (*     repeat red in CONC_FIN. *)
  (*     destruct CONC_FIN as (?&?&?&?&?). *)
  (*     destruct_err_ub_oom x; cbn in H1; inv H1. *)
  (*     destruct H2 as [[] | H2]. *)
  (*     specialize (H2 _ eq_refl). *)
  (*     cbn in H2. *)
  (*     repeat red in H2. *)
  (*     destruct H2 as (?&?&?&?&?). *)
  (*     destruct_err_ub_oom x; cbn in H2; rewrite <- H2 in H4; inv H4. *)
  (*     destruct H3 as [[] | H3]. *)
  (*     specialize (H3 _ eq_refl). *)
  (*     break_match_hyp; try rewrite <- H3 in H6; inv H6. *)
  (*     break_match_hyp; try rewrite <- H3 in H5; inv H5. *)
  (*     rewrite <- H3 in H2; cbn in H2. *)

  (*     specialize (IHuv_inf_u _ H0). *)
  (*     destruct x1; cbn in Heqs; inv Heqs. *)
  (*     break_match_hyp_inv. *)
  (*     break_match_hyp_inv. *)

  (*     pose proof addr_convert_succeeds a as (a'&AA'). *)
  (*     pose proof addr_convert_succeeds a0 as (a0'&A0A0'). *)
  (*     epose proof (handle_gep_addr_fin_inf _ _ _ _ _ _ _ Heqs AA' A0A0' eq_refl). *)

  (*     rewrite IS1.MEM.CP.CONC.concretize_equation. *)
  (*     red. *)
  (*     rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation. *)

  (*     repeat red. *)
  (*     exists (ret (fin_to_inf_dvalue (DVALUE_Addr a))). *)
  (*     exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 (DVALUE_Addr a)))). *)
  (*     rewrite <- H2. *)
  (*     split; eauto. *)
  (*     split; cbn; eauto. *)

  (*     right. *)
  (*     intros a1 ?; subst. *)
  (*     repeat red. *)
  (*     exists (ret (fmap fin_to_inf_dvalue x3)). *)
  (*     exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 x3))). *)
  (*     cbn. *)
  (*     split; eauto. *)
  (*     { clear - H H1 Heqo0. *)
  (*       apply map_monad_oom_Forall2 in Heqo0. *)
  (*       generalize dependent x3. *)
  (*       induction Heqo0; intros x3 H1. *)
  (*       - cbn in *; inv H1; cbn; auto. *)
  (*       - forward IHHeqo0. *)
  (*         { intros idx H2 uv_fin H3. *)
  (*           eapply H; eauto; right; auto. *)
  (*         } *)

  (*         rewrite map_monad_unfold in H1. *)
  (*         repeat red in H1. *)
  (*         destruct H1 as (?&?&?&?&?). *)
  (*         destruct_err_ub_oom x0; inv H2. *)
  (*         destruct H3 as [[] | H3]. *)
  (*         specialize (H3 _ eq_refl). *)

  (*         repeat red in H3. *)
  (*         destruct H3 as (?&?&?&?&?). *)
  (*         rewrite <- H3 in H5. *)
  (*         destruct_err_ub_oom x0; inv H5. *)

  (*         destruct H4 as [[] | H4]. *)
  (*         specialize (H4 _ eq_refl). *)
  (*         cbn in H4. *)

  (*         rewrite <- H4 in H7; inv H7. *)
  (*         cbn in H3; rewrite <- H4 in H3; inv H3. *)

  (*         specialize (IHHeqo0 _ H2). *)
  (*         rewrite map_monad_unfold. *)
  (*         repeat red. *)

  (*         pose proof (H x (or_introl eq_refl) _ H0 _ H1). *)

  (*         exists (ret (fin_to_inf_dvalue x2)). *)
  (*         exists (fun dv_inf => fmap (fmap fin_to_inf_dvalue) (x1 x2)). *)

  (*         cbn; rewrite <- H6; cbn. *)
  (*         split; eauto. *)
  (*         split; eauto. *)

  (*         right. *)
  (*         intros a ?; subst. *)
  (*         repeat red. *)
  (*         exists (ret (fmap fin_to_inf_dvalue x5)). *)
  (*         exists (fun dv_inf => (fmap (fmap fin_to_inf_dvalue) (x4 x5))). *)

  (*         cbn; rewrite <- H4; cbn. *)
  (*         split; eauto. *)
  (*         split; eauto. *)

  (*         right. *)
  (*         intros a ?; subst. *)
  (*         auto. *)
  (*     } *)

  (*     cbn; rewrite <- H3; cbn. *)
  (*     split; eauto. *)

  (*     right. *)
  (*     intros a1 ?; subst. *)
  (*     unfold fin_to_inf_dvalue at 1. *)
  (*     break_inner_match_goal; clear Heqs0; destruct p; clear e0. *)
  (*     cbn in e. *)
  (*     rewrite AA' in e. *)
  (*     inv e. *)
  (*     cbn. *)

  (*     replace (map fin_to_inf_dvalue x3) with (fmap fin_to_inf_dvalue x3) in H4 by reflexivity. *)
  (*     cbn in H4. *)
  (*     rewrite H4. *)

  (*     unfold fin_to_inf_dvalue. *)
  (*     break_match_goal; clear Heqs0; destruct p; clear e0. *)
  (*     cbn in e. *)
  (*     rewrite A0A0' in e. *)
  (*     inv e. *)
  (*     reflexivity. *)
  (*   - (* ExtractElement *) *)
  (*     red; intros dv_fin CONC_FIN. *)
  (*     red in REF. *)
  (*     cbn in REF. *)
  (*     break_match_hyp_inv. *)
  (*     break_match_hyp_inv. *)

  (*     pose proof (IHuv_inf1 u Heqo) as IHuv_inf_u. *)
  (*     pose proof (IHuv_inf2 u0 Heqo0) as IHuv_inf_u0. *)

  (*     unfold uvalue_concretize_fin_inf_inclusion in IHuv_inf_u, IHuv_inf_u0. *)

  (*     rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN. *)
  (*     red in CONC_FIN. *)
  (*     rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN. *)

  (*     repeat red in CONC_FIN. *)
  (*     destruct CONC_FIN as (?&?&?&?&?). *)
  (*     destruct_err_ub_oom x; inv H0. *)
  (*     destruct H1 as [[] | H1]. *)
  (*     specialize (H1 _ eq_refl). *)
  (*     cbn in H1. *)
  (*     repeat red in H1. *)
  (*     destruct H1 as (?&?&?&?&?). *)
  (*     destruct_err_ub_oom x; cbn in H1; rewrite <- H1 in H3; inv H3. *)
  (*     destruct H2 as [[] | H2]. *)
  (*     specialize (H2 _ eq_refl). *)

  (*     repeat red in H2. *)
  (*     destruct H2 as (?&?&?&?&?). *)
  (*     destruct_err_ub_oom x; cbn in H3; rewrite <- H3 in H5; inv H5. *)
  (*     destruct H4 as [[] | H4]. *)
  (*     specialize (H4 _ eq_refl). *)

  (*     remember (x4 x5) as x4x5. *)
  (*     destruct_err_ub_oom x4x5; inv H7. *)
  (*     cbn in H3. *)
  (*     rewrite <- H3 in H1. *)
  (*     cbn in H1. *)

  (*     break_match_hyp_inv. *)

  (*     specialize (IHuv_inf_u _ H). *)
  (*     specialize (IHuv_inf_u0 _ H0). *)

  (*     rewrite IS1.MEM.CP.CONC.concretize_equation. *)
  (*     red. *)
  (*     rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation. *)

  (*     repeat red. *)
  (*     exists (ret (fin_to_inf_dvalue x1)). *)
  (*     exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))). *)
  (*     cbn. *)
  (*     rewrite <- H1. *)
  (*     cbn. *)
  (*     split; eauto. *)
  (*     split; eauto. *)

  (*     right. *)
  (*     intros a ?; subst. *)
  (*     repeat red. *)
  (*     exists (ret (fin_to_inf_dvalue x3)). *)
  (*     exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 x3))). *)
  (*     cbn; rewrite <- H3; cbn. *)
  (*     split; eauto. *)
  (*     split; eauto. *)

  (*     right. *)
  (*     intros a ?; subst. *)
  (*     repeat red. *)
  (*     exists (ret x5). *)
  (*     exists (fun x5 => fmap fin_to_inf_dvalue (x4 x5)). *)
  (*     cbn; rewrite <- Heqx4x5; cbn. *)
  (*     split; eauto. *)
  (*     split; eauto. *)

  (*     right. *)
  (*     intros a ?; subst. *)
  (*     cbn; rewrite <- Heqx4x5; cbn. *)

  (*     eapply index_into_vec_dv_fin_inf; eauto. *)
  (*   - (* InsertElement *) *)
  (*     red; intros dv_fin CONC_FIN. *)
  (*     red in REF. *)
  (*     cbn in REF. *)
  (*     break_match_hyp_inv. *)
  (*     break_match_hyp_inv. *)
  (*     break_match_hyp_inv. *)

  (*     pose proof (IHuv_inf1 u Heqo) as IHuv_inf_u. *)
  (*     pose proof (IHuv_inf2 u0 Heqo0) as IHuv_inf_u0. *)
  (*     pose proof (IHuv_inf3 u1 Heqo1) as IHuv_inf_u1. *)

  (*     unfold uvalue_concretize_fin_inf_inclusion in IHuv_inf_u, IHuv_inf_u0, IHuv_inf_u1. *)

  (*     rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN. *)
  (*     red in CONC_FIN. *)
  (*     rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN. *)

  (*     repeat red in CONC_FIN. *)
  (*     destruct CONC_FIN as (?&?&?&?&?). *)
  (*     destruct_err_ub_oom x; inv H0. *)
  (*     destruct H1 as [[] | H1]. *)
  (*     specialize (H1 _ eq_refl). *)
  (*     cbn in H1. *)

  (*     repeat red in H1. *)
  (*     destruct H1 as (?&?&?&?&?). *)
  (*     destruct_err_ub_oom x; cbn in H1; rewrite <- H1 in H3; inv H3. *)
  (*     destruct H2 as [[] | H2]. *)
  (*     specialize (H2 _ eq_refl). *)

  (*     repeat red in H2. *)
  (*     destruct H2 as (?&?&?&?&?). *)
  (*     destruct_err_ub_oom x; cbn in H3; rewrite <- H3 in H5; inv H5. *)
  (*     destruct H4 as [[] | H4]. *)
  (*     specialize (H4 _ eq_refl). *)

  (*     remember (x4 x5) as x4x5. *)
  (*     destruct_err_ub_oom x4x5; inv H7. *)
  (*     cbn in H3. *)
  (*     rewrite <- H3 in H1. *)
  (*     cbn in H1. *)

  (*     specialize (IHuv_inf_u _ H). *)
  (*     specialize (IHuv_inf_u0 _ H2). *)
  (*     specialize (IHuv_inf_u1 _ H0). *)

  (*     rewrite IS1.MEM.CP.CONC.concretize_equation. *)
  (*     red. *)
  (*     rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation. *)

  (*     repeat red. *)
  (*     exists (ret (fin_to_inf_dvalue x1)). *)
  (*     exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))). *)
  (*     cbn. *)
  (*     rewrite <- H1. *)
  (*     cbn. *)
  (*     split; eauto. *)
  (*     split; eauto. *)

  (*     right. *)
  (*     intros a ?; subst. *)
  (*     repeat red. *)
  (*     exists (ret (fin_to_inf_dvalue x3)). *)
  (*     exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 x3))). *)
  (*     cbn; rewrite <- H3; cbn. *)
  (*     split; eauto. *)
  (*     split; eauto. *)

  (*     right. *)
  (*     intros a ?; subst. *)
  (*     repeat red. *)
  (*     exists (ret (fin_to_inf_dvalue x5)). *)
  (*     exists (fun dv_inf => (fmap fin_to_inf_dvalue (x4 x5))). *)
  (*     cbn; rewrite <- Heqx4x5; cbn. *)
  (*     split; eauto. *)
  (*     split; eauto. *)

  (*     right. *)
  (*     intros a ?; subst. *)

  (*     eapply insert_into_vec_dv_fin_inf; eauto. *)
  (*   - (* ShuffleVector *) *)
  (*     red; intros dv_fin CONC_FIN. *)
  (*     red in REF. *)
  (*     cbn in REF. *)
  (*     break_match_hyp_inv. *)
  (*     break_match_hyp_inv. *)
  (*     break_match_hyp_inv. *)

  (*     pose proof (IHuv_inf1 u Heqo) as IHuv_inf_u. *)
  (*     pose proof (IHuv_inf2 u0 Heqo0) as IHuv_inf_u0. *)
  (*     pose proof (IHuv_inf3 u1 Heqo1) as IHuv_inf_u1. *)

  (*     unfold uvalue_concretize_fin_inf_inclusion in IHuv_inf_u, IHuv_inf_u0, IHuv_inf_u1. *)

  (*     rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN. *)
  (*     red in CONC_FIN. *)
  (*     rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN. *)
  (*     inv CONC_FIN. *)
  (*   - (* ExtractValue *) *)
  (*     red; intros dv_fin CONC_FIN. *)
  (*     red in REF. *)
  (*     cbn in REF. *)
  (*     break_match_hyp_inv. *)

  (*     rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN. *)
  (*     red in CONC_FIN. *)
  (*     rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN. *)
  (*     cbn in CONC_FIN. *)
  (*     repeat red in CONC_FIN. *)

  (*     destruct CONC_FIN as (?&?&?&?&?). *)
  (*     destruct_err_ub_oom x; inv H0. *)
  (*     destruct H1 as [[] | H1]. *)
  (*     specialize (H1 _ eq_refl). *)

  (*     remember (x0 x1) as x0x1. *)
  (*     destruct_err_ub_oom x0x1; inv H3. *)
  (*     apply extract_value_loop_fin_inf_succeeds in H1. *)

  (*     rewrite IS1.MEM.CP.CONC.concretize_equation; *)
  (*       red; rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation; *)
  (*       cbn; repeat red. *)

  (*     exists (ret (fin_to_inf_dvalue x1)). *)
  (*     exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))). *)
  (*     cbn; rewrite <- Heqx0x1; cbn. *)
  (*     split. *)
  (*     eapply IHuv_inf; eauto. *)
  (*     split; eauto. *)

  (*     right. *)
  (*     intros a ?; subst. *)
  (*     auto. *)
  (*   - (* InsertValue *) *)
  (*     red; intros dv_fin CONC_FIN. *)
  (*     red in REF. *)
  (*     cbn in REF. *)
  (*     break_match_hyp_inv. *)
  (*     break_match_hyp_inv. *)

  (*     pose proof (IHuv_inf1 u Heqo) as IHuv_inf_u. *)
  (*     pose proof (IHuv_inf2 u0 Heqo0) as IHuv_inf_u0. *)
  (*     red in IHuv_inf_u, IHuv_inf_u0. *)

  (*     rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN. *)
  (*     red in CONC_FIN. *)
  (*     rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN. *)
  (*     cbn in CONC_FIN. *)

  (*     repeat red in CONC_FIN. *)
  (*     destruct CONC_FIN as (?&?&?&?&?). *)
  (*     destruct_err_ub_oom x; inv H0. *)
  (*     destruct H1 as [[] | H1]. *)
  (*     specialize (H1 _ eq_refl). *)

  (*     repeat red in H1. *)
  (*     destruct H1 as (?&?&?&?&?). *)
  (*     rewrite <- H1 in H3. *)
  (*     destruct_err_ub_oom x; inv H3. *)
  (*     cbn in H1. *)
  (*     destruct H2 as [[] | H2]. *)
  (*     specialize (H2 _ eq_refl). *)

  (*     specialize (IHuv_inf_u _ H). *)
  (*     specialize (IHuv_inf_u0 _ H0). *)

  (*     rewrite IS1.MEM.CP.CONC.concretize_equation; *)
  (*       red; rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation; *)
  (*       cbn; repeat red. *)

  (*     exists (ret (fin_to_inf_dvalue x1)). *)
  (*     exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))). *)
  (*     cbn; rewrite <- H1, H5; cbn. *)
  (*     split; eauto. *)
  (*     split; eauto. *)

  (*     right. *)
  (*     intros a ?; subst. *)
  (*     repeat red. *)

  (*     exists (ret (fin_to_inf_dvalue x3)). *)
  (*     exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 x3))). *)
  (*     cbn; rewrite H5; cbn. *)
  (*     split; eauto. *)
  (*     split; eauto. *)

  (*     right. *)
  (*     intros a ?; subst. *)
  (*     eapply insert_value_loop_fin_inf_succeeds in H2. *)
  (*     setoid_rewrite H2. *)
  (*     remember (x2 x3) as x2x3. *)
  (*     destruct_err_ub_oom x2x3; inv H5. *)
  (*     reflexivity. *)
  (*   - (* Select *) *)
  (*     red; intros dv_fin CONC_FIN. *)
  (*     red in REF. *)
  (*     cbn in REF. *)
  (*     break_match_hyp_inv. *)
  (*     break_match_hyp_inv. *)
  (*     break_match_hyp_inv. *)

  (*     pose proof (IHuv_inf1 u Heqo) as IHuv_inf_u. *)
  (*     pose proof (IHuv_inf2 u0 Heqo0) as IHuv_inf_u0. *)
  (*     pose proof (IHuv_inf3 u1 Heqo1) as IHuv_inf_u1. *)
  (*     red in IHuv_inf_u, IHuv_inf_u0, IHuv_inf_u1. *)

  (*     rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN. *)
  (*     red in CONC_FIN. *)
  (*     rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN. *)
  (*     cbn in CONC_FIN. *)

  (*     repeat red in CONC_FIN. *)
  (*     destruct CONC_FIN as (?&?&?&?&?). *)
  (*     destruct_err_ub_oom x; inv H0. *)
  (*     destruct H1 as [[] | H1]. *)
  (*     specialize (H1 _ eq_refl). *)

  (*     remember (x0 x1) as x0x1. *)
  (*     destruct_err_ub_oom x0x1; inv H3. *)
  (*     pose proof eval_select_fin_inf x1 u0 u1 _ _ dv_fin IHuv_inf_u0 IHuv_inf_u1 H1 as EVAL. *)

  (*     rewrite IS1.MEM.CP.CONC.concretize_equation; *)
  (*       red; rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation; *)
  (*       cbn; repeat red. *)

  (*     specialize (IHuv_inf_u _ H). *)

  (*     exists (ret (fin_to_inf_dvalue x1)). *)
  (*     exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))). *)
  (*     split; eauto. *)
  (*     split; cbn; rewrite <- Heqx0x1; cbn; eauto. *)

  (*     right. *)
  (*     intros a ?; subst. *)
  (*     auto. *)
  (*   - (* ExtractByte *) *)
  (*     red; intros dv_fin CONC_FIN. *)
  (*     red in REF. *)
  (*     cbn in REF. *)
  (*     break_match_hyp_inv. *)
  (*     cbn in *. *)
  (*     inv CONC_FIN. *)
  (*   - (* ConcatBytes *) *)
  (*     cbn in *. *)
  (*     unfold uvalue_concretize_fin_inf_inclusion in *. *)
  (*     intros dv_fin H0. *)

  (*     red in REF. *)
  (*     cbn in REF. *)
  (*     break_match_hyp_inv. *)

  (*     rewrite IS1.MEM.CP.CONC.concretize_equation; *)
  (*       red; rewrite IS1.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation; *)
  (*       cbn; repeat red. *)

  (*     admit. *)
  (* Qed. *)

  Lemma all_extract_bytes_from_uvalue_helper_fin_inf :
    forall uv_bytes_inf uv_bytes_fin uv_inf uv_fin ix sid dt,
      uvalue_refine_strict uv_inf uv_fin ->
      map_monad uvalue_convert_strict uv_bytes_inf = NoOom uv_bytes_fin ->
      IS1.LLVM.MEM.CP.CONCBASE.all_extract_bytes_from_uvalue_helper ix sid dt uv_inf uv_bytes_inf =
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
        rewrite Util.eq_dec_eq in Heqo5; inv Heqo5.
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
      IS1.LLVM.MEM.CP.CONCBASE.all_extract_bytes_from_uvalue dt uv_bytes_inf =
        fmap fin_to_inf_uvalue (all_extract_bytes_from_uvalue dt uv_bytes_fin).
  Proof.
    intros uv_bytes_inf uv_bytes_fin dt HMAPM.
    unfold IS1.LLVM.MEM.CP.CONCBASE.all_extract_bytes_from_uvalue,
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

  Lemma uvalue_concretize_strict_concretize_inclusion :
    forall uv_inf uv_fin,
      uvalue_refine_strict uv_inf uv_fin ->
      uvalue_concretize_fin_inf_inclusion uv_inf uv_fin.
  Proof.
    intros uv_inf.
    induction uv_inf; intros uv_fin REF;
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
        - rewrite map_length.

          apply map_monad_ErrUbOomProp_length in MAP.
          apply Util.Forall2_length in Heqo.
          congruence.
        - intros i a b NTH_fields NTH_res.

          epose proof Util.Forall2_Nth_left NTH_fields Heqo as (x&NTHl&CONV).

          apply Util.Nth_In in NTH_fields.
          specialize (H a NTH_fields x CONV).

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
        - rewrite map_length.

          apply map_monad_ErrUbOomProp_length in MAP.
          apply Util.Forall2_length in Heqo.
          congruence.
        - intros i a b NTH_fields NTH_res.

          epose proof Util.Forall2_Nth_left NTH_fields Heqo as (x&NTHl&CONV).

          apply Util.Nth_In in NTH_fields.
          specialize (H a NTH_fields x CONV).

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
      exists (fun fields => ret (IS1.LP.Events.DV.DVALUE_Array fields)).
      split.
      { eapply map_monad_ErrUbOomProp_forall2.
        apply Util.Forall2_forall.
        split.
        - rewrite map_length.

          apply map_monad_ErrUbOomProp_length in MAP.
          apply Util.Forall2_length in Heqo.
          congruence.
        - intros i a b NTH_fields NTH_res.

          epose proof Util.Forall2_Nth_left NTH_fields Heqo as (x&NTHl&CONV).

          apply Util.Nth_In in NTH_fields.
          specialize (H a NTH_fields x CONV).

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
      exists (fun fields => ret (IS1.LP.Events.DV.DVALUE_Vector fields)).
      split.
      { eapply map_monad_ErrUbOomProp_forall2.
        apply Util.Forall2_forall.
        split.
        - rewrite map_length.

          apply map_monad_ErrUbOomProp_length in MAP.
          apply Util.Forall2_length in Heqo.
          congruence.
        - intros i a b NTH_fields NTH_res.

          epose proof Util.Forall2_Nth_left NTH_fields Heqo as (x&NTHl&CONV).

          apply Util.Nth_In in NTH_fields.
          specialize (H a NTH_fields x CONV).

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

      unfold uvalue_concretize_fin_inf_inclusion in IHuv_inf1, IHuv_inf2.

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
      destruct_err_ub_oom x; cbn in H0; inv H0.
      destruct H1 as [[] | H1].
      specialize (H1 _ eq_refl).
      cbn in H1.
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; rewrite <- H1 in H3; inv H3.
      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).
      rewrite <- H2 in H5, H1.

      remember (eval_iop iop x1 x3) as x1x3.
      destruct_err_ub_oom x1x3; inv H5.
      cbn in H1.

      apply IHuv_inf1 in H.
      apply IHuv_inf2 in H0.

      repeat red.
      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))).
      cbn.
      rewrite <- H1.
      cbn.
      split; eauto.
      split; eauto.

      right.
      intros a H3.
      repeat red.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 x3))).
      cbn.
      rewrite <- H2.
      cbn.
      split; eauto.
      split; eauto.

      right.
      intros a0 H4.

      eapply eval_iop_fin_inf; eauto.
    - (* ICmp *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      break_match_hyp_inv.

      unfold uvalue_concretize_fin_inf_inclusion in IHuv_inf1, IHuv_inf2.

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
      destruct_err_ub_oom x; cbn in H0; inv H0.
      destruct H1 as [[] | H1].
      specialize (H1 _ eq_refl).
      cbn in H1.
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; rewrite <- H1 in H3; inv H3.
      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).
      rewrite <- H2 in H5, H1.

      remember (eval_icmp cmp0 x1 x3) as x1x3.
      destruct_err_ub_oom x1x3; inv H5.
      cbn in H1.

      apply IHuv_inf1 in H.
      apply IHuv_inf2 in H0.

      repeat red.
      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))).
      cbn.
      rewrite <- H1.
      cbn.
      split; eauto.
      split; eauto.

      right.
      intros a H3.
      repeat red.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 x3))).
      cbn.
      rewrite <- H2.
      cbn.
      split; eauto.
      split; eauto.

      right.
      intros a0 H4.

      eapply eval_icmp_fin_inf; eauto.
    - (* FBinop *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      break_match_hyp_inv.

      unfold uvalue_concretize_fin_inf_inclusion in IHuv_inf1, IHuv_inf2.

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
      destruct_err_ub_oom x; cbn in H0; inv H0.
      destruct H1 as [[] | H1].
      specialize (H1 _ eq_refl).
      cbn in H1.
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; rewrite <- H1 in H3; inv H3.
      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).
      rewrite <- H2 in H5, H1.

      remember (eval_fop fop x1 x3) as x1x3.
      destruct_err_ub_oom x1x3; inv H5.
      cbn in H1.

      apply IHuv_inf1 in H.
      apply IHuv_inf2 in H0.

      repeat red.
      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))).
      cbn.
      rewrite <- H1.
      cbn.
      split; eauto.
      split; eauto.

      right.
      intros a H3.
      repeat red.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 x3))).
      cbn.
      rewrite <- H2.
      cbn.
      split; eauto.
      split; eauto.

      right.
      intros a0 H4.

      eapply eval_fop_fin_inf; eauto.
    - (* fcmp *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      break_match_hyp_inv.

      unfold uvalue_concretize_fin_inf_inclusion in IHuv_inf1, IHuv_inf2.

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
      destruct_err_ub_oom x; cbn in H0; inv H0.
      destruct H1 as [[] | H1].
      specialize (H1 _ eq_refl).
      cbn in H1.
      repeat red in H1.
      destruct H1 as (?&?&?&?&?).
      destruct_err_ub_oom x; cbn in H1; rewrite <- H1 in H3; inv H3.
      destruct H2 as [[] | H2].
      specialize (H2 _ eq_refl).
      rewrite <- H2 in H5, H1.

      remember (eval_fcmp cmp0 x1 x3) as x1x3.
      destruct_err_ub_oom x1x3; inv H5.
      cbn in H1.

      apply IHuv_inf1 in H.
      apply IHuv_inf2 in H0.

      repeat red.
      exists (ret (fin_to_inf_dvalue x1)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x0 x1))).
      cbn.
      rewrite <- H1.
      cbn.
      split; eauto.
      split; eauto.

      right.
      intros a H3.
      repeat red.
      exists (ret (fin_to_inf_dvalue x3)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 x3))).
      cbn.
      rewrite <- H2.
      cbn.
      split; eauto.
      split; eauto.

      right.
      intros a0 H4.

      eapply eval_fcmp_fin_inf; eauto.
    - (* Conversion *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.

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
        admit.
      }

      { (* Conv_ItoP *)
        break_match_hyp;
          rewrite <- H1 in H3; inv H3.

        pose proof get_conv_case_itop_fin_inf _ _ _ _ _ Heqc as CONV.
        rewrite CONV.
        admit.
      }

      { (* Conv_PtoI *)
        admit.
      }

      { (* Conv_Illegal *)
        exfalso.
        rewrite <- H1 in H3; inv H3.
      }
    - (* GetElementPtr *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      break_match_hyp_inv.

      pose proof (IHuv_inf u Heqo) as IHuv_inf_u.
      unfold uvalue_concretize_fin_inf_inclusion in IHuv_inf_u.

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
      break_match_hyp; try rewrite <- H3 in H6; inv H6.
      break_match_hyp; try rewrite <- H3 in H5; inv H5.
      rewrite <- H3 in H2; cbn in H2.

      specialize (IHuv_inf_u _ H0).
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
      rewrite <- H2.
      split; eauto.
      split; cbn; eauto.

      right.
      intros a1 ?; subst.
      repeat red.
      exists (ret (fmap fin_to_inf_dvalue x3)).
      exists (fun dv_inf => (fmap fin_to_inf_dvalue (x2 x3))).
      cbn.
      split; eauto.
      { clear - H H1 Heqo0.
        apply map_monad_oom_Forall2 in Heqo0.
        generalize dependent x3.
        induction Heqo0; intros x3 H1.
        - cbn in *; inv H1; cbn; auto.
        - forward IHHeqo0.
          { intros idx H2 uv_fin H3.
            eapply H; eauto; right; auto.
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

          pose proof (H x (or_introl eq_refl) _ H0 _ H1).

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

      cbn; rewrite <- H3; cbn.
      split; eauto.

      right.
      intros a1 ?; subst.
      unfold fin_to_inf_dvalue at 1.
      break_inner_match_goal; clear Heqs0; destruct p; clear e0.
      cbn in e.
      rewrite AA' in e.
      inv e.
      cbn.

      replace (map fin_to_inf_dvalue x3) with (fmap fin_to_inf_dvalue x3) in H4 by reflexivity.
      cbn in H4.
      rewrite H4.

      unfold fin_to_inf_dvalue.
      break_match_goal; clear Heqs0; destruct p; clear e0.
      cbn in e.
      rewrite A0A0' in e.
      inv e.
      reflexivity.
    - (* ExtractElement *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      break_match_hyp_inv.

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
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      break_match_hyp_inv.
      break_match_hyp_inv.

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
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      break_match_hyp_inv.
      break_match_hyp_inv.

      pose proof (IHuv_inf1 u Heqo) as IHuv_inf_u.
      pose proof (IHuv_inf2 u0 Heqo0) as IHuv_inf_u0.
      pose proof (IHuv_inf3 u1 Heqo1) as IHuv_inf_u1.

      unfold uvalue_concretize_fin_inf_inclusion in IHuv_inf_u, IHuv_inf_u0, IHuv_inf_u1.

      rewrite IS2.MEM.CP.CONC.concretize_equation in CONC_FIN.
      red in CONC_FIN.
      rewrite IS2.LLVM.MEM.CP.CONCBASE.concretize_uvalueM_equation in CONC_FIN.
      inv CONC_FIN.
    - (* ExtractValue *)
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
      eapply IHuv_inf; eauto.
      split; eauto.

      right.
      intros a ?; subst.
      auto.
    - (* InsertValue *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      break_match_hyp_inv.

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
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      break_match_hyp_inv.
      break_match_hyp_inv.

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
      pose proof eval_select_fin_inf x1 u0 u1 _ _ dv_fin IHuv_inf_u0 IHuv_inf_u1 H1 as EVAL.

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
      auto.
    - (* ExtractByte *)
      red; intros dv_fin CONC_FIN.
      red in REF.
      cbn in REF.
      break_match_hyp_inv.
      cbn in *.
      inv CONC_FIN.
    - (* ConcatBytes *)
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

        Lemma extractbytes_to_dvalue_fin_inf :
        forall uvs l dv_fin dt
          (Heqo : map_monad uvalue_convert_strict uvs = NoOom l)
          (IH : forall u : DV1.uvalue,
              In u uvs ->
              forall uv_fin : DV2.uvalue,
                uvalue_refine_strict u uv_fin ->
                forall dv_fin : dvalue,
                  IS2.MEM.CP.CONC.concretize uv_fin dv_fin ->
                  IS1.MEM.CP.CONC.concretize u (fin_to_inf_dvalue dv_fin)),
          @extractbytes_to_dvalue ErrUbOomProp Monad_ErrUbOomProp
            (fun (dt : dtyp) (edv : err_ub_oom dvalue) =>
               match @unERR_UB_OOM IdentityMonad.ident dvalue edv with
               | {|
                   EitherMonad.unEitherT :=
                     {|
                       EitherMonad.unEitherT :=
                         {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |}
                     |}
                 |} => dvalue_has_dtyp dv dt /\ dv <> DVALUE_Poison dt
               | _ => False
               end) err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
            (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
            (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
            (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
            (fun (A : Type) (x ue : err_ub_oom A) => x = ue) l dt (success_unERR_UB_OOM dv_fin) ->
          @IS1.LLVM.MEM.CP.CONCBASE.extractbytes_to_dvalue ErrUbOomProp Monad_ErrUbOomProp
            (fun (dt0 : dtyp) (edv : err_ub_oom IS1.LP.Events.DV.dvalue) =>
               match @unERR_UB_OOM IdentityMonad.ident IS1.LP.Events.DV.dvalue edv with
               | {|
                   EitherMonad.unEitherT :=
                     {|
                       EitherMonad.unEitherT :=
                         {| EitherMonad.unEitherT := {| IdentityMonad.unIdent := inr (inr (inr dv)) |} |}
                     |}
                 |} => IS1.LP.Events.DV.dvalue_has_dtyp dv dt0 /\ dv <> IS1.LP.Events.DV.DVALUE_Poison dt0
               | _ => False
               end) err_ub_oom (@Monad_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
            (@RAISE_ERROR_err_ub_oom IdentityMonad.ident IdentityMonad.Monad_ident)
            (@RAISE_UB_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
            (@RAISE_OOM_err_ub_oom_T IdentityMonad.ident IdentityMonad.Monad_ident)
            (fun (A : Type) (x ue : err_ub_oom A) => x = ue) uvs dt
            (success_unERR_UB_OOM (fin_to_inf_dvalue dv_fin)).
        Proof.
          induction uvs; intros l dv_fin dt Heqo IH EXTRACT.
          - cbn in Heqo; inv Heqo.
            clear IH.

            (* Painful non-structurally recursive *)
        Admitted.

        eapply extractbytes_to_dvalue_fin_inf; eauto.
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

        eapply H; eauto.
        2: apply convert_fin_to_inf_uvalue_succeeds.
        admit.
      }

      eapply extractbytes_to_dvalue_fin_inf; eauto.
  Admitted.

  Lemma uvalue_concretize_strict_concretize_inclusion_inf_fin :
    forall uv_inf uv_fin,
      uvalue_refine_strict uv_inf uv_fin ->
      uvalue_concretize_inf_fin_inclusion uv_inf uv_fin.
  Proof.
    (* I don't think this is true? *)
    intros uv_inf uv_fin H.
    unfold uvalue_concretize_inf_fin_inclusion.
    intros dv_inf H0.
    (* dv_inf may not have a finite equivalent *)
  Abort.

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
      eapply DVCrev.dvalue_convert_strict_i1_inv in e0.
      subst; auto.
    - unfold fin_to_inf_dvalue in *.
      break_match_hyp; clear Heqs; destruct p; clear e0.
      break_match_hyp_inv; clear Heqs; destruct p; clear e1.
      cbn in e.
      inv e.
      eapply DVCrev.dvalue_convert_strict_i8_inv in e0.
      subst; auto.
    - unfold fin_to_inf_dvalue in *.
      break_match_hyp; clear Heqs; destruct p; clear e0.
      break_match_hyp_inv; clear Heqs; destruct p; clear e1.
      cbn in e.
      inv e.
      eapply DVCrev.dvalue_convert_strict_i16_inv in e0.
      subst; auto.
    - unfold fin_to_inf_dvalue in *.
      break_match_hyp; clear Heqs; destruct p; clear e0.
      break_match_hyp_inv; clear Heqs; destruct p; clear e1.
      cbn in e.
      inv e.
      eapply DVCrev.dvalue_convert_strict_i32_inv in e0.
      subst; auto.
    - unfold fin_to_inf_dvalue in *.
      break_match_hyp; clear Heqs; destruct p; clear e0.
      break_match_hyp_inv; clear Heqs; destruct p; clear e1.
      cbn in e.
      inv e.
      eapply DVCrev.dvalue_convert_strict_i64_inv in e0.
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

  (* TODO: Move this *)
  Lemma dtyp_inhabited_npoison_inf_fin :
    forall dv_inf t,
      dv_inf <> IS1.LP.Events.DV.DVALUE_Poison t ->
      IS1.LP.Events.DV.dvalue_has_dtyp dv_inf t ->
      exists dv_fin,
        dvalue_has_dtyp dv_fin t /\ dv_fin <> DVALUE_Poison t.
  Proof.
    intros dv_inf t NPOISON DTYP.
  Admitted.

  (* Could be the case that OOM happens...

     If uv_inf is an IBinop, for instance...

     64_bit_intmax + 1

     Then the infinite concretization will produce a value, but the
     finite concretization should OOM.
   *)
  Lemma concretize_inf_concretize_fin :
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

  Lemma concretize_no_ub_inf_fin :
    forall uv_inf uv_fin
      (REF : uvalue_refine_strict uv_inf uv_fin)
      (UB : forall ub_msg : string, ~ IS1.LLVM.MEM.CP.CONC.concretize_u uv_inf (UB_unERR_UB_OOM ub_msg)),
    forall ub_msg : string, ~ concretize_u uv_fin (UB_unERR_UB_OOM ub_msg).
  Proof.
    intros uv_inf uv_fin REF UB ub_msg.
    intros CONC.
    eapply UB.
    admit.
  Admitted.

  Lemma concretize_no_err_inf_fin :
    forall uv_inf uv_fin
      (REF : uvalue_refine_strict uv_inf uv_fin)
      (ERR : forall err_msg : string, ~ IS1.LLVM.MEM.CP.CONC.concretize_u uv_inf (ERR_unERR_UB_OOM err_msg)),
    forall err_msg : string, ~ concretize_u uv_fin (ERR_unERR_UB_OOM err_msg).
  Proof.
    intros uv_inf uv_fin REF UB err_msg.
    intros CONC.
    eapply UB.
    admit.
  Admitted.

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

    pose proof concretize_inf_concretize_fin uv_fin.
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

  Print Assumptions uvalue_refine_strict_unique_prop.

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

      assert (uvalue_refine_strict (DV1.UVALUE_Array elts) (DV2.UVALUE_Array l)) as REF.
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

      assert (uvalue_refine_strict (DV1.UVALUE_Array elts) (DV2.UVALUE_Array l)) as REF.
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

      assert (uvalue_refine_strict (DV1.UVALUE_Array elts) (DV2.UVALUE_Array l)) as REF.
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

      assert (uvalue_refine_strict (DV1.UVALUE_Array elts) (DV2.UVALUE_Array l)) as REF.
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

      assert (uvalue_refine_strict (DV1.UVALUE_Array elts) (DV2.UVALUE_Array l)) as REF.
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

      assert (uvalue_refine_strict (DV1.UVALUE_Array elts) (DV2.UVALUE_Array l)) as REF.
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

      assert (uvalue_refine_strict (DV1.UVALUE_Array elts) (DV2.UVALUE_Array l)) as REF.
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

      assert (uvalue_refine_strict (DV1.UVALUE_Array elts) (DV2.UVALUE_Array l)) as REF.
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

      assert (uvalue_refine_strict (DV1.UVALUE_Array elts) (DV2.UVALUE_Array l)) as REF.
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

      assert (uvalue_refine_strict (DV1.UVALUE_Array elts) (DV2.UVALUE_Array l)) as REF.
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

  Lemma uvalue_refine_strict_concretize_poison :
    forall uv1 uv2,
      uvalue_refine_strict uv1 uv2 ->
      (forall dt : dtyp, ~ IS1.LLVM.MEM.CP.CONC.concretize uv1 (IS1.LP.Events.DV.DVALUE_Poison dt)) <->
        (forall dt : dtyp, ~ concretize uv2 (DVALUE_Poison dt)).
  Proof.
    (* This may not be true if uv2 can OOM... *)
    intros uv1 uv2 REF.
    split.
    { intros CONC dt CONTRA.
      induction uv1;
        rewrite uvalue_refine_strict_equation in REF; cbn in REF;
        try
          solve
          [ inv REF; inv CONTRA
          | cbn in REF;
            break_match_hyp_inv; inv CONTRA
          | inv REF;
            cbn in CONTRA;
            inv CONTRA;
            eapply CONC; cbn; eauto
          ].

      all: admit.
    }

    (* May not need this direction *)
  Admitted.

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

  Lemma denote_instr_orutt_strict :
    forall instr,
      orutt instr_E_refine_strict instr_E_res_refine_strict eq
        (IS1.LLVM.D.denote_instr instr)
        (denote_instr instr)
        (OOM:=OOME).
  Proof.
    intros [[id | id] instr].
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
        apply orutt_bind with (RR:=uvalue_refine_strict).
        { break_match.
          - apply orutt_bind with (RR:=Forall2 dvalue_refine_strict).
            + eapply map_monad_orutt2; eauto.
              intros e1 e2 H0.
              apply pickUnique_instr_E_orutt_strict; auto.
            + intros r0 r3 H0.
              unfold ITree.map.
              eapply orutt_bind with (RR:=dvalue_refine_strict).
              { eapply orutt_trigger; cbn; try tauto.
                intros o CONTRA.
                inv CONTRA.
              }

              intros r4 r5 H1.
              eapply orutt_Ret.
              eapply dvalue_refine_strict_dvalue_to_uvalue; eauto.
          - eapply orutt_bind with (RR:=uvalue_refine_strict).
            { apply translate_exp_to_instr_E1E2_orutt_strict.
              apply denote_op_orutt_strict.
            }

            intros r0 r3 H0.
            eapply orutt_trigger; cbn; try tauto.
            intros o CONTRA.
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
        apply orutt_bind with (RR:=uvalue_refine_strict).
        { break_match.
          { apply orutt_bind with (RR:=Forall2 dvalue_refine_strict).
            { eapply map_monad_orutt2; eauto.
              intros e1 e2 H0.
              apply pickUnique_instr_E_orutt_strict; auto.
            }

            intros r0 r3 H0.
            apply orutt_bind with (RR:=dvalue_refine_strict).
            { apply orutt_trigger; cbn; auto.
              intros t1 t2 H1.
              apply H1.

              intros o CONTRA; inv CONTRA.
            }

            intros r4 r5 H1.
            apply orutt_Ret.
            apply dvalue_refine_strict_dvalue_to_uvalue; auto.
          }

          { apply orutt_bind with (RR:=uvalue_refine_strict).
            { apply translate_exp_to_instr_E1E2_orutt_strict.
              apply denote_exp_E1E2_orutt.
            }

            intros r0 r3 H0.
            apply orutt_trigger; cbn; auto.
            intros t1 t2 H1.
            apply H1.

            intros o CONTRA; inv CONTRA.
          }
        }

        intros r0 r3 H0.
        apply orutt_Ret; auto.
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
      break_match; unfold dvalue_refine_strict in *; cbn in *; try break_match_hyp; inv H0;
        try
          solve
          [ solve_orutt_raise
          ].

      break_match; apply orutt_Ret; auto.
      solve_orutt_raiseUB.
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
              try break_match_hyp_inv; try inv fst_rel;
              cbn; try solve_orutt_raise.
            break_match_goal; cbn; eauto.
            apply orutt_Ret; auto.
          + destruct H2; cbn in *; subst.
            destruct d0; red in fst_rel;
              cbn in fst_rel;
              try break_match_hyp_inv; try inv fst_rel;
              cbn; try solve_orutt_raise.
            break_match_goal; cbn; eauto.
            apply orutt_Ret; auto.
          + destruct H2; cbn in *; subst.
            destruct d0; red in fst_rel;
              cbn in fst_rel;
              try break_match_hyp_inv; try inv fst_rel;
              cbn; try solve_orutt_raise.
            break_match_goal; cbn; eauto.
            apply orutt_Ret; auto.
          + destruct H2; cbn in *; subst.
            destruct d0; red in fst_rel;
              cbn in fst_rel;
              try break_match_hyp_inv; try inv fst_rel;
              cbn; try solve_orutt_raise.
            break_match_goal; cbn; eauto.
            apply orutt_Ret; auto.
      }
    - solve_orutt_raise.
    - solve_orutt_raise.
    - solve_orutt_raise.
    - solve_orutt_raiseUB.
  Qed.

  Lemma denote_block_orutt_strict :
    forall block bid,
      orutt instr_E_refine_strict instr_E_res_refine_strict (sum_rel eq uvalue_refine_strict)
        (IS1.LLVM.D.denote_block block bid)
        (denote_block block bid)
        (OOM:=OOME).
  Proof.
    intros block bid.
    cbn.
    apply orutt_bind with (RR:=eq).
    { apply denote_phis_orutt_strict. }

    intros [] [] _.
    apply orutt_bind with (RR:=eq).
    { apply orutt_bind with (RR:=Forall2 eq).
      { eapply map_monad_orutt.
        eapply denote_instr_orutt_strict.
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
    forall cfg bids,
      orutt instr_E_refine_strict instr_E_res_refine_strict (sum_rel (eq × eq) uvalue_refine_strict)
        (IS1.LLVM.D.denote_ocfg cfg bids)
        (denote_ocfg cfg bids)
        (OOM:=OOME).
  Proof.
    intros cfg [bid_from bid_src].
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
            eapply denote_instr_orutt_strict.
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

  Lemma address_one_function_E1E2_orutt :
    forall dfn,
      orutt event_refine_strict event_res_refine_strict (dvalue_refine_strict × function_denotation_refine_strict)
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
    apply orutt_Ret.

    constructor.
    - cbn; auto.
    - cbn.
      red.
      intros args1 args2 ARGS.
      cbn.
      eapply orutt_bind with (RR:=Forall2 (eq × uvalue_refine_strict)).
      { cbn.
        pose proof (Util.Forall2_length ARGS) as LEN.
        destruct (combine_lists_err (LLVMAst.df_args dfn) args1) eqn:HARGS1.
        { (* Error, means args1 differs in length *)
          (* Currently combine_lists_err does not ever error... This
             may change in the future.*)
          apply combine_lists_err_inl_contra in HARGS1.
          contradiction.
        }

        { assert (length args1 = length args2) as ARGSLEN by eauto using Util.Forall2_length.
          cbn.
          destruct (combine_lists_err (LLVMAst.df_args dfn) args2) eqn:HARGS2.
          apply combine_lists_err_inl_contra in HARGS2; contradiction.

          (* I know args2 is a uvalue refinement of args1.

             I also know that in HARGS1 and HARGS2, args1 and args2
             are being combined with the same list.

             This should mean that `l` and `l0` have the same length...

             And also something like...

             Forall2 (eq × uvalue_refine) l l0
           *)

          assert (Forall2 (eq × uvalue_refine_strict) l l0) as LL0.
          { assert (length l = length l0) as LENLL0.
            { eapply combine_lists_err_length_eq; eauto.
            }

            cbn.
            apply Util.Forall2_forall.
            split; auto.

            intros i a b NTHl NTHl0.
            destruct a as [a1 a2].
            destruct b as [b1 b2].
            epose proof (combine_lists_err_Nth_inv _ _ _ _ _ _ NTHl HARGS1) as [AARGS AARGS1].
            epose proof (combine_lists_err_Nth_inv _ _ _ _ _ _ NTHl0 HARGS2) as [BARGS BARGS1].

            constructor; cbn.
            - cbn in *.
              rewrite AARGS in BARGS.
              inv BARGS.
              reflexivity.
            - eapply Util.Forall2_Nth; eauto.
          }

          cbn.
          apply orutt_Ret; auto.
        }
      }


      intros params1 params2 PARAMS.
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
          + destruct x as [xid xuv].
            destruct y as [yid yuv].
            inv H.
            cbn in fst_rel, snd_rel. subst.
            constructor; cbn.
            inv IHPARAMS; subst_existT.
            apply alist_refine_cons; auto.
        - intros [] [] _.
          reflexivity.
        - intros o CONTRA; inv CONTRA.
      }

      intros [] [] _.
      eapply orutt_bind with (RR:=uvalue_refine_strict).
      { rewrite translate_bind.
        rewrite translate_bind.

        eapply orutt_bind with (RR:=sum_rel (eq × eq) uvalue_refine_strict).
        { (* ocfg stuff *)
          apply translate_instr_to_L0'_E1E2_orutt_strict.
          apply denote_ocfg_orutt_strict.
        }

        intros r0 r3 H.
        inv H.
        - inv H0.
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
        - do 2 rewrite translate_ret.
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
        (Forall2 (dvalue_refine_strict × function_denotation_refine_strict))
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
      Forall2 (dvalue_refine_strict × function_denotation_refine_strict) dfns1 dfns2 ->
      dvalue_refine_strict r1 r2 ->
      IS1.LLVM.D.lookup_defn r1 dfns1 = Some f_den1 ->
      exists f_den2,
        IS2.LLVM.D.lookup_defn r2 dfns2 = Some f_den2 /\
          function_denotation_refine_strict f_den1 f_den2.
  Proof.
    intros dfns1 dfns2 r1 r2 f_den1 DFNS R1R2 LUP.

    pose proof DFNS as NTH.
    apply Util.Forall2_forall in NTH as [LEN NTH].

    pose proof LUP as LUP'.
    eapply assoc_similar_lookup with
      (xs:=dfns1) (ys:=dfns2) (a:=r1) (b:=f_den1) in LUP';
      eauto.
    2: {
      apply dvalue_refine_strict_R2_injective.
    }

    destruct LUP' as [c [d [i [ASSOC [NTH1 NTH2]]]]].
    exists d.

    pose proof (NTH i (r1, f_den1) (c, d) NTH1 NTH2).
    inv H; cbn in *.
    split; auto.

    assert (c = r2) as CR2.
    { eapply dvalue_refine_strict_R2_injective; eauto.
    }

    subst.
    auto.
  Qed.

  (* May not be true with new dvalue_refine *)
  Lemma lookup_defn_none_strict :
    forall dfns1 dfns2 r1 r2,
      Forall2 (dvalue_refine_strict × function_denotation_refine_strict) dfns1 dfns2 ->
      dvalue_refine_strict r1 r2 ->
      IS1.LLVM.D.lookup_defn r1 dfns1 = None ->
      IS2.LLVM.D.lookup_defn r2 dfns2 = None.
  Proof.
    intros dfns1 dfns2 r1 r2 ALL.
    revert r1. revert r2.
    induction ALL; intros r2 r1 REF LUP;
      cbn in *; auto.

    destruct x, y.
    cbn in *.

    inv H.
    cbn in *.

    break_match_hyp; inv LUP.
    eapply RelDec.neg_rel_dec_correct in Heqb.
    pose proof dvalue_refine_strict_R2_injective _ _ _ _ REF fst_rel.
    assert (d0 <> r2).
    { intros D0R2.
      apply H in D0R2; auto.
    }
    { assert (r2 <> d0) by auto.
      apply RelDec.neg_rel_dec_correct in H2.
      rewrite H2.
      eapply assoc_similar_no_lookup with (xs:=l) (RAC:=dvalue_refine_strict); eauto.
      apply dvalue_refine_strict_R2_injective.
    }
  Qed.

  Lemma denote_mcfg_E1E2_orutt' :
    forall dfns1 dfns2 dt f1 f2 args1 args2,
      (Forall2 (dvalue_refine_strict × function_denotation_refine_strict) dfns1 dfns2) ->
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
      (Forall2 (dvalue_refine_strict × function_denotation_refine_strict) dfns1 dfns2) ->
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
      cbn in H1; inv H1; try break_match_hyp_inv;
      try solve [eapply orutt_raise; [intros * CONTRA; inv CONTRA | constructor; constructor]].

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
              (fun char : Int8.int =>
                 ITree.bind
                   (ITree.iter
                      (fun '(c, bytes, offset) =>
                         if Int8.eq c Int8.zero
                         then Ret (inr (Int8.repr 10 :: bytes))
                         else
                           ITree.bind (LLVM1.i8_str_index strptr offset)
                             (fun next_char : Int8.int => Ret (inl (next_char, c :: bytes, (offset + 1)%Z))))
                      (char, [], 1%Z))
                   (fun bytes : list int8 =>
                      ITree.bind (trigger (IS1.LP.Events.IO_stdout (DList.rev_tail_rec bytes)))
                        (fun _ : unit => Ret (IS1.LP.Events.DV.UVALUE_I8 Int8.zero))))
        | _ => raiseUB "puts got non-address argument"
        end
        match r2 with
        | DVALUE_Addr strptr =>
            ITree.bind (i8_str_index strptr 0)
              (fun char : Int8.int =>
                 ITree.bind
                   (ITree.iter
                      (fun '(c, bytes, offset) =>
                         if Int8.eq c Int8.zero
                         then Ret (inr (Int8.repr 10 :: bytes))
                         else
                           ITree.bind (i8_str_index strptr offset)
                             (fun next_char : Int8.int => Ret (inl (next_char, c :: bytes, (offset + 1)%Z))))
                      (char, [], 1%Z))
                   (fun bytes : list int8 =>
                      ITree.bind (trigger (IO_stdout (DList.rev_tail_rec bytes)))
                        (fun _ : unit => Ret (UVALUE_I8 Int8.zero))))
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

  Lemma address_one_builtin_functions_E1E2_orutt :
    forall dfns1 dfns2,
      Forall2 (eq × function_denotation_refine_strict) dfns1 dfns2 ->
      orutt event_refine_strict event_res_refine_strict
        (Forall2 (dvalue_refine_strict × function_denotation_refine_strict))
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
    eapply orutt_Ret.
    constructor; eauto.
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
      break_match_goal; constructor; eauto.
      constructor; eauto.
      cbn.
      apply puts_denotation_refine_strict.
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
      - apply Forall2_app; auto.
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
          (* Lemma alist_refine_strict_fold_right_add : *)
          (*   forall {K V1 V2} *)
          (*     `{RD_K : @RelDec.RelDec K (@eq K)} *)
          (*     `{RD_K_CORRECT : @RelDec.RelDec_Correct _ eq RD_K} *)
          (*     (R: V1 -> V2 -> Prop) xs ys vs1 vs2, *)
          (*     alist_refine R (vs1 ++ xs) (vs2 ++ ys) -> *)
          (*     alist_refine R (fold_right (fun '(id, v) => FMapAList.alist_add id v) xs vs1) (fold_right (fun '(id, v) => FMapAList.alist_add id v) ys vs2). *)
          (* Proof. *)
          (*   unfold FMapAList.alist_add. *)
          (*   unfold  *)
          (*   hinduction vs1 before vs2; intros vs2 REF. *)
          (*   - destruct vs2. *)
          (*     cbn; auto. *)

          (*     { destruct REF, p. *)
          (*       specialize (H k). *)
          (*       destruct H. *)
          (*       forward H1. *)
          (*       eexists; cbn. *)
          (*       rewrite RelDec.rel_dec_eq_true; auto. *)

          (*       destruct H1. *)
          (*       cbn in H1. *)
          (*       inv H1. *)
          (*     } *)
          (*   - induction vs2. *)
          (*     { destruct REF, a. *)
          (*       specialize (H k). *)
          (*       destruct H. *)
          (*       forward H. *)
          (*       eexists; cbn. *)
          (*       rewrite RelDec.rel_dec_eq_true; auto. *)

          (*       destruct H. *)
          (*       cbn in H. *)
          (*       inv H. *)
          (*     } *)

          (*     { cbn. *)
          (*       destruct REF. *)
          (*       cbn in *. *)
          (*       destruct a, a0. *)
          (*       (* TODO: Ugh, equivalent alists may not be in the same *)
          (*       order *) *)
          (*       eapply alist_refine_add with (x:=(k,v)) (y:=(k0,v0)); cbn; auto. *)
          (*       all: admit. *)
          (*     } *)
          (* Admitted. *)

          (* Lemma alist_refine_remove_cons : *)
          (*   forall {K V1 V2} *)
          (*     `{RD_K : @RelDec.RelDec K (@eq K)} *)
          (*     `{RD_K_CORRECT : @RelDec.RelDec_Correct _ eq RD_K} *)
          (*     (R: V1 -> V2 -> Prop) k1 v1 vs1 k2 v2 vs2, *)
          (*     alist_refine R ((k1,v1) :: vs1) ((k2,v2) :: vs2) -> *)
          (*     alist_refine R ((k1,v1) :: FMapAList.alist_remove k1 vs1) ((k2,v2) :: vs2) *)
          (*   alist_refine R *)
          (*     ((k, v) :: FMapAList.alist_remove k (fold_right (fun '(id, v1) (m : FMapAList.alist K V1) => (id, v1) :: FMapAList.alist_remove id m) [] vs1)) *)
          (*     ((k0, v0) :: FMapAList.alist_remove k0 (fold_right (fun '(id, v1) (m : FMapAList.alist K V2) => (id, v1) :: FMapAList.alist_remove id m) [] vs2)) *)

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
  (IS1 : InterpreterStack) (IS2 : InterpreterStack) (AC1 : AddrConvert IS1.LP.ADDR IS1.LP.PTOI IS2.LP.ADDR IS2.LP.PTOI) (AC2 : AddrConvert IS2.LP.ADDR IS2.LP.PTOI IS1.LP.ADDR IS1.LP.PTOI) (LLVM1 : LLVMTopLevel IS1) (LLVM2 : LLVMTopLevel IS2) (TLR : TopLevelRefinements IS2 LLVM2) (IPS : IPConvertSafe IS2.LP.IP IS1.LP.IP) (ACS : AddrConvertSafe IS2.LP.ADDR IS2.LP.PTOI IS1.LP.ADDR IS1.LP.PTOI AC2 AC1) (DVC : DVConvert IS1.LP IS2.LP AC1 IS1.LP.Events IS2.LP.Events) (DVCrev : DVConvert IS2.LP IS1.LP AC2 IS2.LP.Events IS1.LP.Events) (EC : EventConvert IS1.LP IS2.LP AC1 AC2 IS1.LP.Events IS2.LP.Events DVC DVCrev) (TC : TreeConvert IS1 IS2 AC1 AC2 DVC DVCrev EC) (VMEM_IP_PROP1 : VMemInt_Intptr_Properties IS1.LP.IP) (VMEM_IP_PROP2 : VMemInt_Intptr_Properties IS2.LP.IP) (VMEM_REF : VMemInt_Refine IS1.LP.IP IS2.LP.IP) : LangRefine IS1 IS2 AC1 AC2 LLVM1 LLVM2 TLR IPS ACS DVC DVCrev EC TC VMEM_IP_PROP1 VMEM_IP_PROP2 VMEM_REF.
  Include LangRefine IS1 IS2 AC1 AC2 LLVM1 LLVM2 TLR IPS ACS DVC DVCrev EC TC VMEM_IP_PROP1 VMEM_IP_PROP2 VMEM_REF.
End MakeLangRefine.

Module InfFinLangRefine := MakeLangRefine InterpreterStackBigIntptr InterpreterStack64BitIntptr InfToFinAddrConvert FinToInfAddrConvert TopLevelBigIntptr TopLevel64BitIntptr TopLevelRefinements64BitIntptr FinToInfIntptrConvertSafe FinToInfAddrConvertSafe DVCInfFin DVCFinInf ECInfFin TCInfFin VMemInt_Intptr_Properties_Inf VMemInt_Intptr_Properties_Fin VMemInt_Refine_InfFin.

(* Just planning on using this for L4_convert from finite to infinite events. *)
(* Module FinInfLangRefine := MakeLangRefine InterpreterStack64BitIntptr InterpreterStackBigIntptr FinToInfAddrConvert InfToFinAddrConvert TopLevel64BitIntptr TopLevelBigIntptr TopLevelRefinementsBigIntptr FinToInfIntptrConvertSafe. DVCFinInf DVCInfFin ECFinInf . *)
