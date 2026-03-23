From Stdlib Require Import
  Lia
  ZArith
  Program.Equality.

From Vellvm.Semantics Require Import
  MemoryAddress
  VellvmIntegers
  DynamicValues
  InterpretationStack.

From Vellvm.Utils Require Import
  Error
  Tactics
  ListUtil
  OOMRutt
  OOMRuttProps.

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

  Parameter mequ_refine :
    forall x_fin x_inf y_fin y_inf,
      IP_FIN.to_Z x_fin = IP_INF.to_Z x_inf ->
      IP_FIN.to_Z y_fin = IP_INF.to_Z y_inf ->
      @mequ _ IP_FIN.VMemInt_intptr x_fin y_fin = @mequ _ IP_INF.VMemInt_intptr x_inf y_inf.

  Parameter msamesign_refine :
    forall x_fin y_fin x_inf y_inf,
      IP_FIN.to_Z x_fin = IP_INF.to_Z x_inf ->
      IP_FIN.to_Z y_fin = IP_INF.to_Z y_inf ->
      @msamesign _ IP_FIN.VMemInt_intptr x_fin y_fin = 
        @msamesign _ IP_INF.VMemInt_intptr x_inf y_inf. 
  
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
        rewrite <- Rocqlib.two_power_nat_two_p in POW.
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
        rewrite <- Rocqlib.two_power_nat_two_p in POW.
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
        rewrite <- Rocqlib.two_power_nat_two_p in POW.
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
        rewrite Rocqlib.zeq_true in Heqb; inv Heqb.
    - (* ne *)
      pose proof Integers.eq_spec x_fin y_fin.
      break_match_hyp; subst; cbn;
        unfold negb.
      + rewrite Z.eqb_refl; auto.
      + break_match_goal; auto.
        destruct x_fin, y_fin; cbn in *; subst; cbn in *.
        unfold Integers.eq in Heqb.
        cbn in *.
        assert (intval = intval0) by lia; subst.
        rewrite Rocqlib.zeq_true in Heqb; inv Heqb.
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

  Lemma mequ_refine :
    forall x_fin x_inf y_fin y_inf,
      InterpreterStack64BitIntptr.LP.IP.to_Z x_fin = InterpreterStackBigIntptr.LP.IP.to_Z x_inf ->
      InterpreterStack64BitIntptr.LP.IP.to_Z y_fin = InterpreterStackBigIntptr.LP.IP.to_Z y_inf ->
      @mequ _ InterpreterStack64BitIntptr.LP.IP.VMemInt_intptr x_fin y_fin = @mequ _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr x_inf y_inf.
  Proof.
    intros x_fin x_inf y_fin y_inf X Y.
    unfold InterpreterStack64BitIntptr.LP.IP.to_Z,
      InterpreterStackBigIntptr.LP.IP.to_Z in *;
      subst.
    cbn.
    unfold Integers.eq.
    break_match_goal; lia.
  Qed.

  Lemma msamesign_refine :
    forall x_fin y_fin x_inf y_inf,
      InterpreterStack64BitIntptr.LP.IP.to_Z x_fin = InterpreterStackBigIntptr.LP.IP.to_Z x_inf ->
      InterpreterStack64BitIntptr.LP.IP.to_Z y_fin = InterpreterStackBigIntptr.LP.IP.to_Z y_inf ->
      @msamesign _ InterpreterStack64BitIntptr.LP.IP.VMemInt_intptr x_fin y_fin = @msamesign _ InterpreterStackBigIntptr.LP.IP.VMemInt_intptr x_inf y_inf.
  Proof.
    intros x_fin y_fin x_inf y_inf X Y.
    unfold InterpreterStack64BitIntptr.LP.IP.to_Z,
      InterpreterStackBigIntptr.LP.IP.to_Z in *;
      subst.
    cbn in *. unfold msamesign_Z.
    pose proof Integers.unsigned_range x_fin.
    pose proof Integers.unsigned_range y_fin.
    lia.
  Qed.
End VMemInt_Refine_InfFin.
