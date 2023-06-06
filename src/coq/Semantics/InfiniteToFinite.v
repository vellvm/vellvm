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
  Semantics.InfiniteToFinite.LangRefine
  Syntax.DynamicTypes
  Theory.TopLevelRefinements
  Theory.ContainsUB
  Utils.Error
  Utils.Monads
  Utils.MapMonadExtra
  Utils.PropT
  Utils.InterpProp
  Utils.ListUtil
  Utils.Tactics
  Utils.OOMRutt
  Utils.OOMRuttProps
  Handlers.MemoryModules.FiniteAddresses
  Handlers.MemoryModules.InfiniteAddresses
  Handlers.MemoryModelImplementation.

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

Notation LLVM_syntax :=
  (list (LLVMAst.toplevel_entity
           LLVMAst.typ
           (LLVMAst.block LLVMAst.typ * list (LLVMAst.block LLVMAst.typ)))).

Infix "×" := prod_rel (at level 90, left associativity).

Module InfiniteToFinite.
  (* Import FinInfLangRefine. (* Just planning on using this for L4_convert from finite to infinite events. *) *)
  Import InfFinLangRefine.

  From Vellvm Require Import InterpreterMCFG.

  Import MCFGTheoryBigIntptr.
  Import MCFGTheory64BitIntptr.

  Module TLR_INF := TopLevelRefinementsBigIntptr.
  Module TLR_FIN := TopLevelRefinements64BitIntptr.

  Hint Resolve interp_PropT__mono : paco.

  (* TODO: Move these refine_OOM_h lemmas? *)
  Import Morphisms.


  Module E1 := InterpreterStackBigIntptr.LP.Events.
  Module E2 := InterpreterStack64BitIntptr.LP.Events.

  #[local] Notation E1 := (E1.ExternalCallE +' OOME +' UBE +' DebugE +' FailureE).
  #[local] Notation E2 := (E2.ExternalCallE +' OOME +' UBE +' DebugE +' FailureE).
  #[local] Notation OOM_h := (refine_OOM_handler).

  Module InfLLVM := Vellvm.Semantics.InterpretationStack.InterpreterStackBigIntptr.LLVM.
  Module FinLLVM := Vellvm.Semantics.InterpretationStack.InterpreterStack64BitIntptr.LLVM.

  Module EC1 := ECInfFin.
  Module DVC1 := DVCInfFin.
  Module DVC2 := DVCFinInf.
  Print Module DVC1.
  Module InfMem := MemoryBigIntptr.
  Module FinMem := Memory64BitIntptr.

  Module InfMemMMSP := MemoryBigIntptr.MMEP.MMSP.
  Module FinMemMMSP := Memory64BitIntptr.MMEP.MMSP.

  Module InfMemInterp := MemoryBigIntptr.MEM_SPEC_INTERP.
  Module FinMemInterp := Memory64BitIntptr.MEM_SPEC_INTERP.

  Module InfLP := InterpreterStackBigIntptr.LP.
  Module FinLP := InterpreterStack64BitIntptr.LP.

  (* Module EC2 := EventConvert FinLP InfLP FinToInfAddrConvert InfToFinAddrConvert FinLP.Events InfLP.Events DVC1. *)

  Module DVCS := DVConvertSafe FinLP InfLP FinToInfAddrConvert InfToFinAddrConvert FinToInfAddrConvertSafe FinToInfIntptrConvertSafe FinLP.Events InfLP.Events DVC2 DVC1.
  Import DVCS.

  (* TODO: Should we move this? *)
  Definition addr_refine addr_inf addr_fin := InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin.

  (* TODO: Should we move this? *)
  Definition fin_to_inf_addr (a : FinAddr.addr) : InfAddr.addr.
    unfold FinAddr.addr in a.
    unfold FiniteAddresses.Iptr in a.
    pose proof FinToInfAddrConvertSafe.addr_convert_succeeds a as [a' _].
    exact a'.
  Defined.

  Lemma unsigned_repr_eq:
    forall i, ((0 <=? i)%Z && (i <? Int64.modulus)%Z)%bool = true ->
         Int64.unsigned (Int64.repr i) = i.
  Proof.
    intros i H.
    Transparent Int64.repr.
    unfold Int64.repr.
    unfold Int64.unsigned.
    cbn.
    Opaque Int64.repr.
    symmetry in H.
    apply Bool.andb_true_eq in H.
    destruct H.
    assert (0 <= i < Integers.Int64.modulus)%Z by lia.
    rewrite Integers.Int64.Z_mod_modulus_eq.
    rewrite Zmod_small; auto.
  Qed.
  
  
  Lemma lift_addr_Convert_addr_inverse:
    forall {a_inf a_fin},
        InfToFinAddrConvert.addr_convert a_inf = NoOom a_fin ->
        fin_to_inf_addr a_fin = a_inf.
  Proof.
    intros.
    unfold InfToFinAddrConvert.addr_convert in H.
    destruct a_inf.
    unfold FinITOP.int_to_ptr in H.
    unfold fin_to_inf_addr.
    destruct (((i <? 0)%Z || (i >=? Int64.modulus)%Z)%bool) eqn: HEQ.
    - inversion H.
    - inversion H.
      unfold FiniteAddresses.Prov.
      unfold Prov in *.
      remember (FinToInfAddrConvertSafe.addr_convert_succeeds (Int64.repr i, p)) as X.
      destruct X. destruct x.
      unfold FinToInfAddrConvert.addr_convert in e.
      cbn in e.
      inversion e.
      subst.
      rewrite unsigned_repr_eq; auto.
      apply Bool.orb_false_elim in HEQ.      
      apply andb_true_intro.
      lia.
  Qed.


  (* TODO: Should we move this? *)
  Definition fin_to_inf_dvalue (dv : LLVMParams64BitIntptr.Events.DV.dvalue) : LLVMParamsBigIntptr.Events.DV.dvalue.
    pose proof dvalue_convert_strict_safe dv as [dvi [CONV RCONV]].
    apply dvi.
  Defined.

  (* SAZ: These seem like the basic inversion properties - but things are too opaque? *)
  Lemma fin_to_inf_conbert_dvalue_inversion :
    forall {dv_inf dv_fin},
      DVC1.dvalue_convert_strict dv_inf = NoOom dv_fin ->
      fin_to_inf_dvalue dv_fin = dv_inf.
  Proof.
    intros dv_inf dv_fin H.
    unfold fin_to_inf_dvalue.
  Admitted.


  (* TODO: Should we move this? *)
  Definition fin_to_inf_uvalue (uv : LLVMParams64BitIntptr.Events.DV.uvalue) : LLVMParamsBigIntptr.Events.DV.uvalue.
    pose proof uvalue_convert_strict_safe uv as [uvi [CONV RCONV]].
    apply uvi.
  Defined.

  Lemma convert_fin_to_inf_uvalue_succeeds :
    forall {uv_fin},
      DVC1.uvalue_convert_strict (fin_to_inf_uvalue uv_fin) = NoOom uv_fin.
  Proof.
    intros.
    unfold fin_to_inf_uvalue.
    destruct  (uvalue_convert_strict_safe uv_fin).
    destruct p.
    rewrite e0.
    reflexivity.
  Qed.

  (* SAZ: These seem like the basic inversion properties - but things are too opaque? *)
  Lemma fin_to_inf_convert_uvalue_inversion :
    forall {uv_inf uv_fin},
      DVC1.uvalue_convert_strict uv_inf = NoOom uv_fin ->
      fin_to_inf_uvalue uv_fin = uv_inf.
  Proof.
    intros uv_inf uv_fin H.
    unfold fin_to_inf_uvalue.
  Admitted.


  (* Could not put with the other conversions, need to know what memory structures like MemState are *)
  Definition convert_SByte (sb1 : MemoryBigIntptr.MP.BYTE_IMPL.SByte) : OOM (Memory64BitIntptr.MP.BYTE_IMPL.SByte).
    destruct sb1.
    refine (uv' <- DVC1.uvalue_convert_strict uv;;
            idx' <- DVC1.uvalue_convert_strict idx;;
            ret (FiniteSizeof.mkUByte LLVMParams64BitIntptr.Events.DV.uvalue uv' dt idx' sid)).
  Defined.

  Definition lift_SByte (sb1 : Memory64BitIntptr.MP.BYTE_IMPL.SByte) : MemoryBigIntptr.MP.BYTE_IMPL.SByte.
    destruct sb1.
    remember (DVC2.uvalue_convert_strict uv).
    exact (FiniteSizeof.mkUByte DVC2.DV2.uvalue (fin_to_inf_uvalue uv) dt (fin_to_inf_uvalue idx) sid).
  Defined.

  Lemma lift_SByte_convert_SByte_inverse :
    forall {sb_inf sb_fin},
      convert_SByte sb_inf = NoOom sb_fin ->
      lift_SByte sb_fin = sb_inf.
  Proof.
    intros.
    unfold convert_SByte in H.
    unfold lift_SByte.
    destruct sb_inf eqn: EQ1.
    destruct (DVC1.uvalue_convert_strict uv) eqn: EQ2; [|inversion H].
    cbn in H.
    destruct (DVC1.uvalue_convert_strict idx) eqn: EQ3; [|inversion H].
    inversion H.
    apply fin_to_inf_convert_uvalue_inversion in EQ2.
    apply fin_to_inf_convert_uvalue_inversion in EQ3.
    rewrite EQ2.
    rewrite EQ3.
    reflexivity.
  Qed.

  Definition sbyte_refine byte_inf byte_fin : Prop :=
    convert_SByte byte_inf = NoOom byte_fin.

  Lemma sbyte_refine_lifted :
    forall byte,
      sbyte_refine (lift_SByte byte) byte.
  Proof.
    intros.
    unfold sbyte_refine, lift_SByte.
    destruct byte.
    cbn.
    do 2 rewrite convert_fin_to_inf_uvalue_succeeds.
    reflexivity.
  Qed.

  Definition convert_mem_byte (mb1 : InfMemMMSP.mem_byte) : OOM (FinMemMMSP.mem_byte).
    destruct mb1.
    refine (s' <- convert_SByte s;;
            ret _).

    constructor.
    apply s'.
    apply a.
  Defined.

  Definition lift_mem_byte (mb1 : FinMemMMSP.mem_byte) : InfMemMMSP.mem_byte.
    destruct mb1.
    constructor.
    - exact (lift_SByte s).
    - apply a.
  Defined.

  Lemma lift_mem_byte_convert_mem_byte_inversion :
    forall {mb_inf mb_fin},
      convert_mem_byte mb_inf = NoOom mb_fin ->
      lift_mem_byte mb_fin = mb_inf.
  Proof.
    intros.
    unfold convert_mem_byte in H.
    destruct mb_inf eqn : EQ1.
    destruct (convert_SByte s) eqn: EQ2; [|inversion H].
    cbn in H.
    inversion H.
    apply lift_SByte_convert_SByte_inverse in EQ2.
    cbn.
    rewrite EQ2.
    reflexivity.
  Qed.

  (* Slightly tricky.

     Both the infinite and finite memory have the same underlying
     structure --- a map from Z to mem_bytes.

     The Z indexes in the finite memory may need to be limited to the
     range of the address type, but it may not matter because trying
     to look these up in a program should cause OOM anyway. Currently
     this check is added.
   *)
  Definition convert_memory (mem : InfMemMMSP.memory) : OOM (FinMemMMSP.memory).
    refine (elems <- map_monad _ (IntMaps.IM.elements mem);;
            ret (IntMaps.IP.of_list elems)).

    refine (fun '(ix, mb) =>
              (* Check if address fits in finite memory space :) *)
              LLVMParams64BitIntptr.ITOP.int_to_ptr ix PROV.nil_prov;;
              mb' <- convert_mem_byte mb;;
              ret (ix, mb')).
  Defined.

  Definition lift_memory (mem : FinMemMMSP.memory) : InfMemMMSP.memory :=
    IntMaps.IM.map lift_mem_byte mem.

  Lemma IntMaps_map_list_map_Equal :
    forall {A B} (f : A -> B) l,
      IntMaps.IM.Equal (IntMaps.IM.map f (IntMaps.IP.of_list l)) (IntMaps.IP.of_list (List.map (fun '(i, x) => (i, f x)) l)).
  Proof.
  Admitted.

  Lemma Forall2_cons_inversion :
    forall {A B} f (x:A) (y:B) xs ys,
      Forall2 f (x::xs) (y::ys) -> f x y /\ Forall2 f xs ys.
  Proof.
    intros.
    inversion H; subst.
    tauto.
  Qed.

  Lemma lift_memory_convert_memory_inversion :
    forall {mem_inf mem_fin},
      convert_memory mem_inf = NoOom mem_fin ->
      IntMaps.IM.Equal (lift_memory mem_fin) mem_inf.
  Proof.
    intros mem_inf mem_fin H.
    unfold convert_memory in H.
    unfold lift_memory.
    unfold FinMemMMSP.memory in *.
    unfold IntMaps.IM.key in *.
    destruct (map_monad
        (fun '(ix, mb) =>
         _ <- LLVMParams64BitIntptr.ITOP.int_to_ptr ix PROV.nil_prov;;
         mb' <- convert_mem_byte mb;; ret (ix, mb'))
        (IntMaps.IM.elements (elt:=InfMemMMSP.mem_byte) mem_inf)) eqn: EQ1; [| inversion H].

    cbn in H.
    inversion H.
    subst; clear H.
    apply map_monad_oom_forall2 in EQ1.

    apply IntMaps.IP.F.Equal_mapsto_iff.
    intros.

    rewrite IntMaps_map_list_map_Equal.
    rewrite IntMaps.IP.of_list_1.
    - rewrite (@IntMaps.IP.F.elements_mapsto_iff _ _ k e).
      revert k e.
      remember (fun (a : Z * InfMemMMSP.mem_byte) (b : Z * FinMemMMSP.mem_byte) =>
             (let
            '(ix, mb) := a in
             _ <- LLVMParams64BitIntptr.ITOP.int_to_ptr ix PROV.nil_prov;;
             mb' <- convert_mem_byte mb;;
             ret (ix, mb')) = NoOom b) as body.
      remember (IntMaps.IM.elements (elt:=InfMemMMSP.mem_byte) mem_inf) as l_inf.
      clear mem_inf Heql_inf.
      revert l_inf EQ1.
      induction l; intros.
      + destruct l_inf.
        * intros. reflexivity.
        * inversion EQ1.
      + destruct l_inf.
        * inversion EQ1.
        * inversion EQ1; subst.
          intros.
          destruct p.
          destruct (LLVMParams64BitIntptr.ITOP.int_to_ptr k0 PROV.nil_prov) eqn: EQ2; [|inversion H2].
          cbn in H2.
          destruct (convert_mem_byte m) eqn: EQ3; [|inversion H2].
          inversion H2.
          subst.
          cbn.
          split; intros.
          -- apply SetoidList.InA_cons in H.
             destruct H as [HEQ | HR].
             ++ inversion HEQ.
                cbn in H. cbn in H0.
                subst.
                apply lift_mem_byte_convert_mem_byte_inversion in EQ3.
                rewrite EQ3.
                apply SetoidList.InA_cons_hd. reflexivity.
             ++ apply SetoidList.InA_cons_tl.
                apply IHl.
                apply Forall2_cons_inversion in EQ1.
                destruct EQ1 as [_ H].
                apply H.
                assumption.
          -- apply SetoidList.InA_cons in H.
             destruct H as [HEQ | HR].
             ++ inversion HEQ.
                cbn in H. cbn in H0.
                subst.
                apply lift_mem_byte_convert_mem_byte_inversion in EQ3.
                rewrite EQ3.
                apply SetoidList.InA_cons_hd. reflexivity.
             ++ apply SetoidList.InA_cons_tl.
                apply (@IHl l_inf).
                apply Forall2_cons_inversion in EQ1.
                destruct EQ1 as [_ H].
                apply H.
                assumption.
    - clear k. clear e.
      assert (SetoidList.NoDupA (IntMaps.IM.eq_key (elt:=InfMemMMSP.mem_byte))
                (IntMaps.IM.elements mem_inf)).
      { apply IntMaps.IM.elements_3w. }
      remember (IntMaps.IM.elements (elt:=InfMemMMSP.mem_byte) mem_inf) as l_inf.
      clear mem_inf Heql_inf.
      revert l EQ1.
      induction H; intros.
      + inversion EQ1. subst. cbn. auto.
      + inversion EQ1. subst. cbn.
        destruct x.
        destruct (LLVMParams64BitIntptr.ITOP.int_to_ptr k PROV.nil_prov) eqn: EQ2; [|inversion H3].
        cbn in H3.
        destruct (convert_mem_byte m) eqn: EQ3; [|inversion H3].
        inversion H3.
        subst. clear H3.
        constructor.
        2 : { apply IHNoDupA. assumption. }
        intros X.
        apply H.
        clear H H0 IHNoDupA EQ1 a EQ2 EQ3.

        induction H5.
        * inversion X.
        * destruct x.
          destruct (LLVMParams64BitIntptr.ITOP.int_to_ptr z PROV.nil_prov) eqn: EQ2; [|inversion H].
          cbn in H.
          destruct (convert_mem_byte m1) eqn: EQ3; [|inversion H].
          inversion H.
          subst. clear H.
          apply SetoidList.InA_cons in X.
          destruct X as [HEQ | HR].
          -- apply SetoidList.InA_cons_hd.
             apply HEQ.
          -- apply SetoidList.InA_cons_tl.
             apply IHForall2.
             apply HR.
  Qed.

  Definition convert_Frame (f : InfMemMMSP.Frame) : OOM (FinMemMMSP.Frame).
    induction f.
    - exact (ret []).
    - refine (a' <- InfToFinAddrConvert.addr_convert a;;
              f' <- IHf;;
              ret (a' :: f')).
  Defined.

  Definition lift_Frame (f : FinMemMMSP.Frame) : InfMemMMSP.Frame :=
    map fin_to_inf_addr f.

  Definition convert_FrameStack (fs : InfMemMMSP.FrameStack) : OOM (FinMemMMSP.FrameStack).
    induction fs.
    - refine (f' <- convert_Frame f;;
              ret (FinMemMMSP.Singleton f')).
    - refine (f' <- convert_Frame f;;
              fs' <- IHfs;;
              ret (FinMemMMSP.Snoc fs' f')).
  Defined.

  Definition lift_FrameStack (fs : FinMemMMSP.FrameStack) : InfMemMMSP.FrameStack.
    induction fs.
    - refine (let f' := lift_Frame f in
              InfMemMMSP.Singleton f').
    - refine (let f' := lift_Frame f in
              InfMemMMSP.Snoc IHfs f').
  Defined.

  Definition convert_Block (b : InfMemMMSP.Block) : OOM (FinMemMMSP.Block)
    := map_monad InfToFinAddrConvert.addr_convert b.

  Definition lift_Block (b : FinMemMMSP.Block) : InfMemMMSP.Block
    := map fin_to_inf_addr b.

  Lemma lift_Block_convert_Block_inverse :
    forall {b_inf b_fin},
      convert_Block b_inf = NoOom b_fin ->
      lift_Block b_fin = b_inf.
  Proof.
  Admitted.


  Definition convert_Heap (h : InfMemMMSP.Heap) : OOM (FinMemMMSP.Heap).
    refine (blocks <- map_monad _ (IntMaps.IM.elements h);;
            ret (IntMaps.IP.of_list blocks)).

    refine (fun '(ix, b) =>
              b' <- convert_Block b;;
              ret (ix, b')).
  Defined.

  Definition in_bounds (z:Z) : bool :=
    match LLVMParams64BitIntptr.ITOP.int_to_ptr z PROV.nil_prov with
    | NoOom _ => true
    | Oom _ => false
    end.

  Lemma in_bounds_Z : forall (z:Z), in_bounds z = ((0 <=? z)%Z && (z <? Int64.modulus)%Z)%bool.
  Proof.
    intros z.
    unfold in_bounds.
    unfold LLVMParams64BitIntptr.ITOP.int_to_ptr.
    break_match; break_match_hyp; inversion Heqo; lia.
  Qed.


  Lemma in_bounds_exists_addr : forall z (p:Prov), in_bounds z = true <-> exists addr, LLVMParams64BitIntptr.PTOI.ptr_to_int addr = z /\ snd addr = p.
  Proof.
    intros.
    unfold in_bounds.
    split; intros H.
    - break_match_hyp. exists (fst a, p).
      split; auto.
      unfold LLVMParams64BitIntptr.ITOP.int_to_ptr in Heqo.
      break_match_hyp; inversion Heqo.
      unfold LLVMParams64BitIntptr.PTOI.ptr_to_int. cbn.
      apply unsigned_repr_eq. lia.
      inversion H.
    - destruct H as [ptr [HP HPROV]].
      subst.
      unfold LLVMParams64BitIntptr.ITOP.int_to_ptr.
      unfold LLVMParams64BitIntptr.PTOI.ptr_to_int.
      break_match.
      break_match_hyp; inversion Heqo.
      reflexivity.
      break_match_hyp; inversion Heqo.
      destruct ptr.
      clear Heqo H0.
      cbn in *.
      rewrite <- Heqb.
      unfold FiniteAddresses.Iptr in i.
      destruct i.
      cbn.
      lia.
  Qed.

  Lemma filter_dom_map_eq :
    forall {A B} (f : IntMaps.IM.key -> bool) (g : A -> B) (m : IntMaps.IntMap A) ,
      forall k e,
        IntMaps.IM.MapsTo k e (IntMaps.IM.map g (IntMaps.IP.filter_dom f m))
        <->
          IntMaps.IM.MapsTo k e (IntMaps.IP.filter_dom f (IntMaps.IM.map g m)).
  Proof.
    intros.
    unfold IntMaps.IP.filter_dom.
    split; intros H.
    - rewrite IntMaps.IP.filter_iff.
      apply IntMaps.IP.F.map_mapsto_iff in H.
      destruct H as [a [EQ HM]].
      apply IntMaps.IP.filter_iff in HM.
      destruct HM.
      split; auto.
      apply IntMaps.IP.F.map_mapsto_iff.
      exists a. tauto.
      repeat red; intros; subst; auto.
      repeat red; intros; subst; auto.
    - rewrite IntMaps.IP.filter_iff in H.
      destruct H.
      apply IntMaps.IP.F.map_mapsto_iff in H.
      destruct H as [a [EQ HM]].
      apply IntMaps.IP.F.map_mapsto_iff.
      exists a. split; auto.
      apply IntMaps.IP.filter_iff; auto.
      repeat red; intros; subst; auto.
      repeat red; intros; subst; auto.
  Qed.

  Lemma MapsTo_filter_true :
    forall {A} (f : IntMaps.IM.key -> A -> bool) m,
    forall k e,
      f k e = true ->
      IntMaps.IM.MapsTo k e m <->
        IntMaps.IM.MapsTo k e (IntMaps.IP.filter f m).
  Proof.
    intros.
    split; intros.
    - apply IntMaps.IP.filter_iff.
      + repeat red; intros; subst; auto.
      + tauto.
    - apply IntMaps.IP.filter_iff in H0.
      + tauto.
      + repeat red; intros; subst; auto.
  Qed.

  Lemma MapsTo_filter_subset :
    forall {A} (f : IntMaps.IM.key -> A -> bool) m,
    forall k e,
      IntMaps.IM.MapsTo k e (IntMaps.IP.filter f m) ->
      IntMaps.IM.MapsTo k e m.
  Proof.
    intros.
    apply IntMaps.IP.filter_iff in H.
    + tauto.
    + repeat red; intros; subst; auto.
  Qed.

  Lemma not_MapsTo_filter :
    forall {A} (f : IntMaps.IM.key -> A -> bool) m,
    forall k e,
      ~ IntMaps.IM.MapsTo k e m ->
      ~ IntMaps.IM.MapsTo k e (IntMaps.IP.filter f m).
  Proof.
    intros.
    intro C.
    apply H.
    eapply MapsTo_filter_subset.
    eauto.
  Qed.
  
  Lemma MapsTo_filter_dom_true :
    forall {A} (f : IntMaps.IM.key -> bool) (m : IntMaps.IntMap A),
    forall k e,
      f k = true ->
      IntMaps.IM.MapsTo k e m <->
        IntMaps.IM.MapsTo k e (IntMaps.IP.filter_dom f m).
  Proof.
    intros.
    unfold IntMaps.IP.filter_dom.
    apply MapsTo_filter_true.
    assumption.
  Qed.

  Lemma MapsTo_filter_dom_subset :
    forall {A} (f : IntMaps.IM.key -> bool) (m : IntMaps.IntMap A),
    forall k e,
      IntMaps.IM.MapsTo k e (IntMaps.IP.filter_dom f m) ->      
      IntMaps.IM.MapsTo k e m.
  Proof.
    intros.
    unfold IntMaps.IP.filter_dom.
    eapply MapsTo_filter_subset.
    eauto.
  Qed.

  Lemma not_MapsTo_filter_dom :
    forall {A} (f : IntMaps.IM.key -> bool) (m : IntMaps.IntMap A),
    forall k e,
      ~ IntMaps.IM.MapsTo k e m ->
      ~ IntMaps.IM.MapsTo k e (IntMaps.IP.filter_dom f m).
  Proof.
    intros.
    intro C.
    apply H.
    eapply MapsTo_filter_dom_subset.
    eauto.
  Qed.
  
  Lemma find_filter_true :
    forall {A} (f : IntMaps.IM.key -> A -> bool) (m : IntMaps.IntMap A),
      forall k a,
        IntMaps.IM.find k (IntMaps.IP.filter f m) = Some a <->
          IntMaps.IM.find k m = Some a /\ (f k a = true).
  Proof.
    intros.
    split; intros H.
    - apply IntMaps.IP.F.find_mapsto_iff in H.
      apply IntMaps.IP.filter_iff in H.
      destruct H.
      split; auto.
      apply IntMaps.IP.F.find_mapsto_iff. assumption.
      repeat red; intros; subst; auto.
    - destruct H.
      apply IntMaps.IP.F.find_mapsto_iff.
      apply IntMaps.IP.filter_iff.
      repeat red; intros; subst; auto.
      apply IntMaps.IP.F.find_mapsto_iff in H.      
      split; auto.
  Qed.

  Lemma find_filter_dom_true : 
    forall {A} (f : IntMaps.IM.key -> bool) (m : IntMaps.IntMap A),
      forall k a,
        IntMaps.IM.find k (IntMaps.IP.filter_dom f m) = Some a <->
          IntMaps.IM.find k m = Some a /\ (f k = true).
  Proof.
    intros.
    unfold IntMaps.IP.filter_dom.
    apply find_filter_true.
  Qed.

  Lemma IntMaps_find_None :
    forall {A} (k : IntMaps.IM.key) (m:IntMaps.IntMap A),
      IntMaps.IM.find k m = None <-> forall e, ~ IntMaps.IM.MapsTo k e m.
  Proof.
    intros.
    split; intros H.
    - intros. intro C.
      apply IntMaps.IP.F.find_mapsto_iff in C.
      rewrite H in C. inversion C.
    - destruct (IntMaps.IM.find k m) eqn:EQ; auto.
      apply IntMaps.IP.F.find_mapsto_iff in EQ.
      apply H in EQ.
      contradiction.
  Qed.
    
  Lemma find_filter_None :
    forall {A} (f : IntMaps.IM.key -> A -> bool) (m : IntMaps.IntMap A),
    forall k,
      IntMaps.IM.find k m = None ->
        IntMaps.IM.find k (IntMaps.IP.filter f m) = None.
  Proof.
    intros.
    rewrite IntMaps_find_None.
    intros e C.
    rewrite IntMaps_find_None in H.
    specialize (H e).
    apply H.
    apply (MapsTo_filter_subset f m).
    auto.
  Qed.

  Lemma find_filter_dom_None :
    forall {A} (f : IntMaps.IM.key -> bool) (m : IntMaps.IntMap A),
    forall k,
      IntMaps.IM.find k m = None ->
        IntMaps.IM.find k (IntMaps.IP.filter_dom f m) = None.
  Proof.
    intros.
    unfold IntMaps.IP.filter_dom.
    apply find_filter_None.
    assumption.
  Qed.

  Definition lift_Heap (h : FinMemMMSP.Heap) : InfMemMMSP.Heap
    :=
    let h' := IntMaps.IP.filter_dom in_bounds h in
    IntMaps.IM.map lift_Block h'.

  Lemma lift_Heap_convert_Heap_inverse :
    forall {h_inf h_fin},
      convert_Heap h_inf = NoOom h_fin ->
      lift_Heap h_fin = h_inf.
  Proof.
  Admitted.


  Definition convert_memory_stack (ms1 : InfMemMMSP.memory_stack) : OOM (FinMemMMSP.memory_stack).
    destruct ms1 as [mem fs h].
    refine (mem' <- convert_memory mem;;
            fs' <- convert_FrameStack fs;;
            h' <- convert_Heap h;;
            ret _).

    constructor; auto.
  Defined.

  Definition lift_memory_stack (ms1 : FinMemMMSP.memory_stack) : InfMemMMSP.memory_stack.
    destruct ms1 as [mem fs h].
    refine (let mem' := lift_memory mem in
            let fs' := lift_FrameStack fs in
            let h' := lift_Heap h in
            _).

    constructor; auto.
  Defined.

  (* TODO: Move this *)
  Lemma lift_memory_stack_convert_memory_stack_inverse :
    forall {ms_inf ms_fin},
      convert_memory_stack ms_inf = NoOom ms_fin ->
      lift_memory_stack ms_fin = ms_inf.
  Proof.
  Admitted.


  Definition convert_MemState (m1 : InfMem.MMEP.MMSP.MemState) : OOM (FinMem.MMEP.MMSP.MemState).
    destruct m1 as [ms pr].
    refine (ms' <- convert_memory_stack ms;;
            ret _).

    constructor; auto.
  Defined.

  Definition lift_MemState (m1 : FinMem.MMEP.MMSP.MemState) : InfMem.MMEP.MMSP.MemState.
    destruct m1 as [ms pr].
    refine (let ms' := lift_memory_stack ms in
            _).

    constructor; auto.
  Defined.

  Definition MemState_refine (m1 : InfMem.MMEP.MMSP.MemState) (m2 : FinMem.MMEP.MMSP.MemState) : Prop
    := convert_MemState m1 = NoOom m2.

  Lemma MemState_refine_initial :
    MemState_refine InfMemMMSP.initial_memory_state FinMemMMSP.initial_memory_state.
  Proof.
    reflexivity.
  Qed.

  (* TODO: Move this *)
  Lemma lift_MemState_convert_MemState_inverse :
    forall {ms_inf ms_fin},
      convert_MemState ms_inf = NoOom ms_fin ->
      lift_MemState ms_fin = ms_inf.
  Proof.
    intros.
    unfold lift_MemState.
    destruct ms_fin. cbn in *.
    destruct ms_inf.
    cbn in *.

  Admitted.

  (* TODO: Move this *)
  Lemma MemState_fin_to_inf_to_fin :
    forall ms,
      convert_MemState (lift_MemState ms) = NoOom ms.
  Proof.
    intros ms.
  Admitted.

  Definition Heap_in_bounds (ms_fin:FinMem.MMEP.MMSP.MemState) : Prop :=
    let h := Memory64BitIntptr.MMEP.MMSP.mem_state_heap ms_fin in
    forall i, is_true (IntMaps.member i h) -> exists ptr, FinPTOI.ptr_to_int ptr = i.

  (* TODO: Need a MemState_refine_prop that takes all of the predicates
      like write_byte_all_preserved and bundles them in one place
      between memories. Should use this for these lemmas... *)
  (* TODO: Confirm and move this *)
  Definition MemState_refine_prop ms_inf ms_fin :=
    let ms_fin_lifted := lift_MemState ms_fin in
    InfMem.MMEP.MemSpec.preserve_allocation_ids ms_inf ms_fin_lifted /\
      InfMem.MMEP.MemSpec.read_byte_preserved ms_inf ms_fin_lifted /\
      InfMem.MMEP.MemSpec.write_byte_allowed_all_preserved ms_inf ms_fin_lifted /\
      InfMem.MMEP.MemSpec.free_byte_allowed_all_preserved ms_inf ms_fin_lifted /\
      InfMem.MMEP.MemSpec.allocations_preserved ms_inf ms_fin_lifted /\
      InfMem.MMEP.MemSpec.frame_stack_preserved ms_inf ms_fin_lifted /\
      InfMem.MMEP.MemSpec.heap_preserved ms_inf ms_fin_lifted /\
      Heap_in_bounds ms_fin.


  (* TODO: move this *)
  (*
  Lemma MemState_refine_MemState_refine_prop :
    forall ms_inf ms_fin,
      MemState_refine ms_inf ms_fin ->
      MemState_refine_prop ms_inf ms_fin.
  Proof.
    intros ms_inf ms_fin MSR.
    red.
    red in MSR.
    erewrite lift_MemState_convert_MemState_inverse; eauto.
    split; [|split; [|split; [|split; [|split; [|split]]]]]; try (red; reflexivity).

    split; split; [red; reflexivity|].
  Qed.
   *)

  Definition sbytes_refine bytes_inf bytes_fin : Prop :=
    Forall2 sbyte_refine bytes_inf bytes_fin.

  (** More refinement relations *)
  Definition L3_E1E2_orutt_strict (t1 : PropT InfLP.Events.L3 (InfMemMMSP.MemState *
                                                                 (MemPropT.store_id * (InfLLVM.Local.local_env * InfLLVM.Stack.lstack * (InfLLVM.Global.global_env * InfLP.Events.DV.dvalue))))) t2
    : Prop :=
    forall t', t2 t' ->
               exists t, t1 t /\
                           orutt
                             L3_refine_strict
                             L3_res_refine_strict
                             (MemState_refine × (eq × (local_refine_strict × stack_refine_strict × (global_refine_strict × DVC1.dvalue_refine_strict))))
                             t t' (OOM:=OOME).

  Definition model_E1E2_L3_orutt_strict p1 p2 :=
    L3_E1E2_orutt_strict
      (TopLevelBigIntptr.model_oom_L3 p1)
      (TopLevel64BitIntptr.model_oom_L3 p2).

  Definition lift_local_env (lenv : InterpreterStack64BitIntptr.LLVM.Local.local_env) : InterpreterStackBigIntptr.LLVM.Local.local_env.
    refine (map _ lenv).

    refine (fun '(ix, uv) =>
              let uv' := fin_to_inf_uvalue uv in
              (ix, uv')).
  Defined.

  Definition lift_global_env (genv : InterpreterStack64BitIntptr.LLVM.Global.global_env) : InterpreterStackBigIntptr.LLVM.Global.global_env.
    refine (map _ genv).

    refine (fun '(ix, dv) =>
              let dv' := fin_to_inf_dvalue dv in
              (ix, dv')).
  Defined.

  Definition lift_stack (stack : InterpreterStack64BitIntptr.LLVM.Stack.lstack) : InterpreterStackBigIntptr.LLVM.Stack.lstack.
    induction stack.
    - exact [].
    - exact (lift_local_env a :: IHstack).
  Defined.

  Unset Implicit Arguments.
  Unset Contextual Implicit.
  Definition get_inf_tree' :
    forall (t_fin2 : itree L3 (FinMem.MMEP.MMSP.MemState * (MemPropT.store_id * (local_env * @stack local_env * res_L1)))), itree InfLP.Events.L3 TopLevelBigIntptr.res_L6.
  Proof.
    cofix CIH.
    intros t_fin2.
    destruct t_fin2.
    destruct _observe.
    - (* Ret *)
      refine (ret _).
      destruct r as [ms [sid [[lenv s] [genv res]]]].
      constructor.
      exact (lift_MemState ms).

      constructor.
      exact sid.

      constructor.
      constructor.
      exact (lift_local_env lenv).
      exact (lift_stack s).

      constructor.
      exact (lift_global_env genv).
      exact (fin_to_inf_dvalue res).
    - (*Tau *)
      apply go.
      apply TauF.
      apply CIH.
      apply t.
    - (* Vis *)
      inversion e; clear e; subst.
      { (* ExternalCallE *)
        inversion H; subst.
        apply go.
        apply (VisF (subevent _ (E1.ExternalCall t (fin_to_inf_uvalue f) (map fin_to_inf_dvalue args)))).

        (* Continuation *)
        intros x.
        apply CIH.

        pose proof (DVCInfFin.dvalue_convert_strict x).
        destruct H0.
        - exact (k d).
        - (* OOM -- somewhat worried about this case *)
          exact (raiseOOM s).
      }

      inversion X0; clear X0; subst.
      { (* PickUvalue *)
        inversion X1; subst.
        apply go.
        apply (VisF (subevent _ (E1.pick Pre (fin_to_inf_uvalue x)))).

        (* Continuation *)
        intros res.
        destruct res.
        apply CIH.

        pose proof (DVCInfFin.dvalue_convert_strict x0).
        destruct H.
        - apply k.
          constructor.
          apply d.
          apply t.
        - (* OOM -- somewhat worried about this case *)
          exact (raiseOOM s).
      }

      inversion H; clear H; subst.
      { (* OOM *)
        inversion H0; subst.
        exact (raiseOOM H).
      }

      inversion H0; clear H0; subst.
      { (* UBE *)
        inversion H; subst.
        exact (raiseUB H0).
      }

      inversion H; clear H; subst.
      { (* DebugE *)
        inversion H0; subst.
        apply go.
        apply (VisF (subevent _ (Debug H))).
        intros H1.
        apply CIH.
        apply k; auto.
      }

      { (* FailureE *)
        inversion H0; subst.
        exact (LLVMEvents.raise H).
      }

      Show Proof.
  Defined.

  Set Printing All.
  Set Printing Implicit.
  Set Printing Depth 1000.


  Unset Printing All.
  Unset Printing Implicit.
  Definition get_inf_tree :
    forall (t_fin2 : itree L3 (FinMem.MMEP.MMSP.MemState * (MemPropT.store_id * (local_env * @stack local_env * res_L1)))), itree InfLP.Events.L3 TopLevelBigIntptr.res_L6 :=
    cofix CIH (t_fin2 : itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) :
      itree InfLP.Events.L3
        (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
      (fun _observe : itreeF L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue)))) (itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) =>
         match
           _observe
           return
           (itree InfLP.Events.L3
              (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
         with
         | RetF r =>
             (fun r0 : prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))) =>
                @ret (itree InfLP.Events.L3) (@Monad_itree InfLP.Events.L3)
                  (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                  match
                    r0 return (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                  with
                  | pair a b =>
                      (fun (ms : FinMem.MMEP.MMSP.MemState) (p : prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))) =>
                         match
                           p
                           return
                           (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                         with
                         | pair a0 b0 =>
                             (fun (sid : MemPropT.store_id) (p0 : prod (prod local_env (@stack local_env)) (prod global_env dvalue)) =>
                                match
                                  p0
                                  return
                                  (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                with
                                | pair a1 b1 =>
                                    (fun p1 : prod local_env (@stack local_env) =>
                                       match
                                         p1
                                         return
                                         (forall _ : prod global_env dvalue,
                                             prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                               (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                       with
                                       | pair a2 b2 =>
                                           (fun (lenv : local_env) (s : @stack local_env) (p2 : prod global_env dvalue) =>
                                              match
                                                p2
                                                return
                                                (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                   (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                              with
                                              | pair a3 b3 =>
                                                  (fun (genv : global_env) (res : dvalue) =>
                                                     @pair InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                       (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))) (lift_MemState ms)
                                                       (@pair MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)) sid
                                                          (@pair (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)
                                                             (@pair InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack (lift_local_env lenv) (lift_stack s))
                                                             (@pair InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue (lift_global_env genv) (fin_to_inf_dvalue res))))) a3 b3
                                              end) a2 b2
                                       end) a1 b1
                                end) a0 b0
                         end) a b
                  end) r
         | TauF t =>
             (fun t0 : itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue)))) =>
                @go InfLP.Events.L3
                  (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                  (@TauF InfLP.Events.L3
                     (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                     (itree InfLP.Events.L3
                        (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                     (CIH t0))) t
         | @VisF _ _ _ X e k =>
             (fun (X0 : Type) (e0 : L3 X0) (k0 : forall _ : X0, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) =>
                let X1 :
                  itree InfLP.Events.L3
                    (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                  match
                    e0
                    return
                    (itree InfLP.Events.L3
                       (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                  with
                  | inl1 x =>
                      (fun H : ExternalCallE X0 =>
                         (fun H0 : ExternalCallE X0 =>
                            let X1 :
                              forall _ : @eq Type X0 X0,
                                itree InfLP.Events.L3
                                  (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                              match
                                H0 in (ExternalCallE T)
                                return
                                (forall _ : @eq Type T X0,
                                    itree InfLP.Events.L3
                                      (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                         (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                              with
                              | ExternalCall t f args =>
                                  (fun (t0 : dtyp) (f0 : uvalue) (args0 : list dvalue) (H1 : @eq Type dvalue X0) =>
                                     (fun H2 : @eq Type dvalue X0 =>
                                        let H3 : @eq Type dvalue X0 := H2 in
                                        @eq_rect Type dvalue
                                          (fun _ : Type =>
                                             forall (_ : dtyp) (_ : uvalue) (_ : list dvalue),
                                               itree InfLP.Events.L3
                                                 (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                    (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                          (fun (t1 : dtyp) (f1 : uvalue) (args1 : list dvalue) =>
                                             @eq_rect Type dvalue
                                               (fun X1 : Type =>
                                                  forall (_ : forall _ : X1, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : ExternalCallE X1),
                                                    itree InfLP.Events.L3
                                                      (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                         (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                               (fun (k1 : forall _ : dvalue, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : ExternalCallE dvalue) =>
                                                  @go InfLP.Events.L3
                                                    (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                       (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                                    (@VisF InfLP.Events.L3
                                                       (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                          (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                                       (itree InfLP.Events.L3
                                                          (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                             (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))) E1.DV.dvalue
                                                       (@subevent E1.ExternalCallE InfLP.Events.L3
                                                          (@ReSum_inl (forall _ : Type, Type) IFun sum1 Cat_IFun Inl_sum1 E1.ExternalCallE InfLP.Events.ExternalCallE (sum1 InfLP.Events.PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) (@ReSum_id (forall _ : Type, Type) IFun Id_IFun InfLP.Events.ExternalCallE)) E1.DV.dvalue
                                                          (E1.ExternalCall t1 (fin_to_inf_uvalue f1) (@map LLVMParams64BitIntptr.Events.DV.dvalue LLVMParamsBigIntptr.Events.DV.dvalue fin_to_inf_dvalue args1)))
                                                       (fun x0 : E1.DV.dvalue =>
                                                          CIH
                                                            (let H5 : OOM DVCInfFin.DV2.dvalue := DVCInfFin.dvalue_convert_strict x0 in
                                                             match H5 return (itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) with
                                                             | NoOom a => (fun d : DVCInfFin.DV2.dvalue => k1 d) a
                                                             | Oom s =>
                                                                 (fun s0 : string =>
                                                                    @raiseOOM L3
                                                                      (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 OOME (sum1 PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) ExternalCallE
                                                                         (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 OOME (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) PickUvalueE
                                                                            (@ReSum_inl (forall _ : Type, Type) IFun sum1 Cat_IFun Inl_sum1 OOME OOME (sum1 UBE (sum1 DebugE FailureE)) (@ReSum_id (forall _ : Type, Type) IFun Id_IFun OOME))))
                                                                      (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue)))) s0) s
                                                             end)))) X0 H2 k0 H0) X0 H3) H1 t0 f0 args0) t f args
                              end in
                                X1 (@eq_refl Type X0)) H) x
                  | inr1 x =>
                      (fun X1 : sum1 PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) X0 =>
                         (fun X2 : sum1 PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) X0 =>
                            let X3 :
                              itree InfLP.Events.L3
                                (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                              match
                                X2
                                return
                                (itree InfLP.Events.L3
                                   (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                      (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                              with
                              | inl1 x0 =>
                                  (fun X3 : PickUvalueE X0 =>
                                     (fun X4 : PickUvalueE X0 =>
                                        let X5 :
                                          forall _ : @eq Type X0 X0,
                                            itree InfLP.Events.L3
                                              (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                 (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                                          match
                                            X4 in (PickE T)
                                            return
                                            (forall _ : @eq Type T X0,
                                                itree InfLP.Events.L3
                                                  (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                     (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                          with
                                          | pick Pre x1 =>
                                              (fun (Pre0 : Prop) (x2 : uvalue) (H : @eq Type (@sig dvalue (fun _ : dvalue => True)) X0) =>
                                                 (fun H0 : @eq Type (@sig dvalue (fun _ : dvalue => True)) X0 =>
                                                    let H1 : @eq Type (@sig dvalue (fun _ : dvalue => True)) X0 := H0 in
                                                    @eq_rect Type (@sig dvalue (fun _ : dvalue => True))
                                                      (fun _ : Type =>
                                                         forall (_ : Prop) (_ : uvalue),
                                                           itree InfLP.Events.L3
                                                             (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                      (fun (Pre1 : Prop) (x3 : uvalue) =>
                                                         @eq_rect Type (@sig dvalue (fun _ : dvalue => True))
                                                           (fun X5 : Type =>
                                                              forall (_ : forall _ : X5, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : PickUvalueE X5),
                                                                itree InfLP.Events.L3
                                                                  (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                     (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                           (fun (k1 : forall _ : @sig dvalue (fun _ : dvalue => True), itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : PickUvalueE (@sig dvalue (fun _ : dvalue => True))) =>
                                                              @go InfLP.Events.L3
                                                                (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                   (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                                                (@VisF InfLP.Events.L3
                                                                   (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                      (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                                                   (itree InfLP.Events.L3
                                                                      (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                         (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                                   (@sig InfLP.Events.DV.dvalue (fun _ : InfLP.Events.DV.dvalue => True))
                                                                   (@subevent (@E1.PickE LLVMParamsBigIntptr.Events.DV.uvalue InfLP.Events.DV.dvalue (fun (_ : InfLP.Events.DV.uvalue) (_ : InfLP.Events.DV.dvalue) => True)) InfLP.Events.L3
                                                                      (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 (@E1.PickE LLVMParamsBigIntptr.Events.DV.uvalue InfLP.Events.DV.dvalue (fun (_ : InfLP.Events.DV.uvalue) (_ : InfLP.Events.DV.dvalue) => True))
                                                                         (sum1 InfLP.Events.PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) InfLP.Events.ExternalCallE
                                                                         (@ReSum_inl (forall _ : Type, Type) IFun sum1 Cat_IFun Inl_sum1 (@E1.PickE LLVMParamsBigIntptr.Events.DV.uvalue InfLP.Events.DV.dvalue (fun (_ : InfLP.Events.DV.uvalue) (_ : InfLP.Events.DV.dvalue) => True)) InfLP.Events.PickUvalueE
                                                                            (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) (@ReSum_id (forall _ : Type, Type) IFun Id_IFun InfLP.Events.PickUvalueE))) (@sig InfLP.Events.DV.dvalue (fun _ : InfLP.Events.DV.dvalue => True))
                                                                      (@E1.pick LLVMParamsBigIntptr.Events.DV.uvalue InfLP.Events.DV.dvalue (fun (_ : InfLP.Events.DV.uvalue) (_ : InfLP.Events.DV.dvalue) => True) Pre1 (fin_to_inf_uvalue x3)))
                                                                   (fun res : @sig InfLP.Events.DV.dvalue (fun _ : InfLP.Events.DV.dvalue => True) =>
                                                                      match
                                                                        res
                                                                        return
                                                                        (itree InfLP.Events.L3
                                                                           (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                              (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                                      with
                                                                      | @exist _ _ x4 p =>
                                                                          (fun (x5 : InfLP.Events.DV.dvalue) (t : True) =>
                                                                             CIH
                                                                               (let H2 : OOM DVCInfFin.DV2.dvalue := DVCInfFin.dvalue_convert_strict x5 in
                                                                                match H2 return (itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) with
                                                                                | NoOom a => (fun d : DVCInfFin.DV2.dvalue => k1 (@exist dvalue (fun _ : dvalue => True) d t)) a
                                                                                | Oom s =>
                                                                                    (fun s0 : string =>
                                                                                       @raiseOOM L3
                                                                                         (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 OOME (sum1 PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) ExternalCallE
                                                                                            (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 OOME (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) PickUvalueE
                                                                                               (@ReSum_inl (forall _ : Type, Type) IFun sum1 Cat_IFun Inl_sum1 OOME OOME (sum1 UBE (sum1 DebugE FailureE)) (@ReSum_id (forall _ : Type, Type) IFun Id_IFun OOME))))
                                                                                         (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue)))) s0) s
                                                                                end)) x4 p
                                                                      end))) X0 H0 k0 X4) X0 H1) H Pre0 x2) Pre x1
                                          end in
                                            X5 (@eq_refl Type X0)) X3) x0
                              | inr1 x0 =>
                                  (fun H : sum1 OOME (sum1 UBE (sum1 DebugE FailureE)) X0 =>
                                     (fun H0 : sum1 OOME (sum1 UBE (sum1 DebugE FailureE)) X0 =>
                                        let X3 :
                                          itree InfLP.Events.L3
                                            (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                               (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                                          match
                                            H0
                                            return
                                            (itree InfLP.Events.L3
                                               (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                  (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                          with
                                          | inl1 x1 =>
                                              (fun H1 : OOME X0 =>
                                                 (fun H2 : OOME X0 =>
                                                    let X3 :
                                                      forall _ : @eq Type X0 X0,
                                                        itree InfLP.Events.L3
                                                          (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                             (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                                                      match
                                                        H2 in (OOME T)
                                                        return
                                                        (forall _ : @eq Type T X0,
                                                            itree InfLP.Events.L3
                                                              (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                 (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                      with
                                                      | ThrowOOM x2 =>
                                                          (fun (H3 : string) (H4 : @eq Type Empty_set X0) =>
                                                             (fun H5 : @eq Type Empty_set X0 =>
                                                                let H6 : @eq Type Empty_set X0 := H5 in
                                                                @eq_rect Type Empty_set
                                                                  (fun _ : Type =>
                                                                     forall _ : string,
                                                                       itree InfLP.Events.L3
                                                                         (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                            (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                                  (fun H7 : string =>
                                                                     @eq_rect Type Empty_set
                                                                       (fun X3 : Type =>
                                                                          forall (_ : forall _ : X3, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : OOME X3),
                                                                            itree InfLP.Events.L3
                                                                              (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                 (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                                       (fun (_ : forall _ : Empty_set, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : OOME Empty_set) =>
                                                                          @raiseOOM InfLP.Events.L3
                                                                            (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 OOME (sum1 InfLP.Events.PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) InfLP.Events.ExternalCallE
                                                                               (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 OOME (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) InfLP.Events.PickUvalueE
                                                                                  (@ReSum_inl (forall _ : Type, Type) IFun sum1 Cat_IFun Inl_sum1 OOME OOME (sum1 UBE (sum1 DebugE FailureE)) (@ReSum_id (forall _ : Type, Type) IFun Id_IFun OOME))))
                                                                            (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                               (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) H7) X0 H5 k0 H2) X0 H6) H4 H3)
                                                            x2
                                                      end in
                                                        X3 (@eq_refl Type X0)) H1) x1
                                          | inr1 x1 =>
                                              (fun H1 : sum1 UBE (sum1 DebugE FailureE) X0 =>
                                                 (fun H2 : sum1 UBE (sum1 DebugE FailureE) X0 =>
                                                    let X3 :
                                                      itree InfLP.Events.L3
                                                        (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                           (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                                                      match
                                                        H2
                                                        return
                                                        (itree InfLP.Events.L3
                                                           (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                              (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                      with
                                                      | inl1 x2 =>
                                                          (fun H3 : UBE X0 =>
                                                             (fun H4 : UBE X0 =>
                                                                let X3 :
                                                                  forall _ : @eq Type X0 X0,
                                                                    itree InfLP.Events.L3
                                                                      (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                         (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                                                                  match
                                                                    H4 in (UBE T)
                                                                    return
                                                                    (forall _ : @eq Type T X0,
                                                                        itree InfLP.Events.L3
                                                                          (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                             (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                                  with
                                                                  | ThrowUB x3 =>
                                                                      (fun (H5 : string) (H6 : @eq Type Empty_set X0) =>
                                                                         (fun H7 : @eq Type Empty_set X0 =>
                                                                            let H8 : @eq Type Empty_set X0 := H7 in
                                                                            @eq_rect Type Empty_set
                                                                              (fun _ : Type =>
                                                                                 forall _ : string,
                                                                                   itree InfLP.Events.L3
                                                                                     (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                        (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                                              (fun H9 : string =>
                                                                                 @eq_rect Type Empty_set
                                                                                   (fun X3 : Type =>
                                                                                      forall (_ : forall _ : X3, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : UBE X3),
                                                                                        itree InfLP.Events.L3
                                                                                          (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                             (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                                                   (fun (_ : forall _ : Empty_set, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : UBE Empty_set) =>
                                                                                      @raiseUB InfLP.Events.L3
                                                                                        (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 UBE (sum1 InfLP.Events.PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) InfLP.Events.ExternalCallE
                                                                                           (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 UBE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) InfLP.Events.PickUvalueE
                                                                                              (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 UBE (sum1 UBE (sum1 DebugE FailureE)) OOME
                                                                                                 (@ReSum_inl (forall _ : Type, Type) IFun sum1 Cat_IFun Inl_sum1 UBE UBE (sum1 DebugE FailureE) (@ReSum_id (forall _ : Type, Type) IFun Id_IFun UBE)))))
                                                                                        (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                           (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) H9) X0 H7 k0 H4) X0 H8)
                                                                           H6 H5) x3
                                                                  end in
                                                                    X3 (@eq_refl Type X0)) H3) x2
                                                      | inr1 x2 =>
                                                          (fun H3 : sum1 DebugE FailureE X0 =>
                                                             (fun H4 : sum1 DebugE FailureE X0 =>
                                                                let X3 :
                                                                  itree InfLP.Events.L3
                                                                    (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                       (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                                                                  match
                                                                    H4
                                                                    return
                                                                    (itree InfLP.Events.L3
                                                                       (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                          (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                                  with
                                                                  | inl1 x3 =>
                                                                      (fun H5 : DebugE X0 =>
                                                                         (fun H6 : DebugE X0 =>
                                                                            let X3 :
                                                                              forall _ : @eq Type X0 X0,
                                                                                itree InfLP.Events.L3
                                                                                  (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                     (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                                                                              match
                                                                                H6 in (DebugE T)
                                                                                return
                                                                                (forall _ : @eq Type T X0,
                                                                                    itree InfLP.Events.L3
                                                                                      (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                         (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                                              with
                                                                              | Debug x4 =>
                                                                                  (fun (H7 : string) (H8 : @eq Type unit X0) =>
                                                                                     (fun H9 : @eq Type unit X0 =>
                                                                                        let H10 : @eq Type unit X0 := H9 in
                                                                                        @eq_rect Type unit
                                                                                          (fun _ : Type =>
                                                                                             forall _ : string,
                                                                                               itree InfLP.Events.L3
                                                                                                 (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                                    (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                                                          (fun H11 : string =>
                                                                                             @eq_rect Type unit
                                                                                               (fun X3 : Type =>
                                                                                                  forall (_ : forall _ : X3, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : DebugE X3),
                                                                                                    itree InfLP.Events.L3
                                                                                                      (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                                         (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                                                               (fun (k1 : forall _ : unit, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : DebugE unit) =>
                                                                                                  @go InfLP.Events.L3
                                                                                                    (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                                       (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                                                                                    (@VisF InfLP.Events.L3
                                                                                                       (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                                          (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                                                                                       (itree InfLP.Events.L3
                                                                                                          (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                                             (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))) unit
                                                                                                       (@subevent DebugE InfLP.Events.L3
                                                                                                          (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 DebugE (sum1 InfLP.Events.PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) InfLP.Events.ExternalCallE
                                                                                                             (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 DebugE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) InfLP.Events.PickUvalueE
                                                                                                                (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 DebugE (sum1 UBE (sum1 DebugE FailureE)) OOME
                                                                                                                   (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 DebugE (sum1 DebugE FailureE) UBE
                                                                                                                      (@ReSum_inl (forall _ : Type, Type) IFun sum1 Cat_IFun Inl_sum1 DebugE DebugE FailureE (@ReSum_id (forall _ : Type, Type) IFun Id_IFun DebugE)))))) unit (Debug H11)) (fun H13 : unit => CIH (k1 H13)))) X0 H9 k0 H6) X0 H10) H8 H7) x4
                                                                              end in
                                                                                X3 (@eq_refl Type X0)) H5) x3
                                                                  | inr1 x3 =>
                                                                      (fun H5 : FailureE X0 =>
                                                                         (fun H6 : FailureE X0 =>
                                                                            let X3 :
                                                                              forall _ : @eq Type X0 X0,
                                                                                itree InfLP.Events.L3
                                                                                  (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                     (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                                                                              match
                                                                                H6 in (FailureE T)
                                                                                return
                                                                                (forall _ : @eq Type T X0,
                                                                                    itree InfLP.Events.L3
                                                                                      (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                         (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                                              with
                                                                              | Throw x4 =>
                                                                                  (fun (H7 : string) (H8 : @eq Type Empty_set X0) =>
                                                                                     (fun H9 : @eq Type Empty_set X0 =>
                                                                                        let H10 : @eq Type Empty_set X0 := H9 in
                                                                                        @eq_rect Type Empty_set
                                                                                          (fun _ : Type =>
                                                                                             forall _ : string,
                                                                                               itree InfLP.Events.L3
                                                                                                 (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                                    (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                                                          (fun H11 : string =>
                                                                                             @eq_rect Type Empty_set
                                                                                               (fun X3 : Type =>
                                                                                                  forall (_ : forall _ : X3, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : FailureE X3),
                                                                                                    itree InfLP.Events.L3
                                                                                                      (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                                         (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                                                               (fun (_ : forall _ : Empty_set, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : FailureE Empty_set) =>
                                                                                                  @LLVMEvents.raise InfLP.Events.L3
                                                                                                    (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                                       (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                                                                                    (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 FailureE (sum1 InfLP.Events.PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) InfLP.Events.ExternalCallE
                                                                                                       (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 FailureE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) InfLP.Events.PickUvalueE
                                                                                                          (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 FailureE (sum1 UBE (sum1 DebugE FailureE)) OOME
                                                                                                             (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 FailureE (sum1 DebugE FailureE) UBE
                                                                                                                (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 FailureE FailureE DebugE (@ReSum_id (forall _ : Type, Type) IFun Id_IFun FailureE)))))) H11) X0 H9 k0 H6) X0 H10) H8 H7) x4
                                                                              end in
                                                                                X3 (@eq_refl Type X0)) H5) x3
                                                                  end in
                                                                X3) H3) x2
                                                      end in
                                                    X3) H1) x1
                                          end in
                                        X3) H) x0
                              end in
                            X3) X1) x
                  end in
                X1) X e k
         end) (@_observe _ _ t_fin2).

  Definition _get_inf_tree (t_fin2 : itree' L3 (FinMem.MMEP.MMSP.MemState * (MemPropT.store_id * (local_env * @stack local_env * res_L1)))) : itree InfLP.Events.L3 TopLevelBigIntptr.res_L6 :=
    match t_fin2 with
    | RetF r =>
        (fun r0 : prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))) =>
           @ret (itree InfLP.Events.L3) (@Monad_itree InfLP.Events.L3)
             (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
             match
               r0 return (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
             with
             | pair a b =>
                 (fun (ms : FinMem.MMEP.MMSP.MemState) (p : prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))) =>
                    match
                      p
                      return
                      (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                    with
                    | pair a0 b0 =>
                        (fun (sid : MemPropT.store_id) (p0 : prod (prod local_env (@stack local_env)) (prod global_env dvalue)) =>
                           match
                             p0
                             return
                             (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                           with
                           | pair a1 b1 =>
                               (fun p1 : prod local_env (@stack local_env) =>
                                  match
                                    p1
                                    return
                                    (forall _ : prod global_env dvalue,
                                        prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                          (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                  with
                                  | pair a2 b2 =>
                                      (fun (lenv : local_env) (s : @stack local_env) (p2 : prod global_env dvalue) =>
                                         match
                                           p2
                                           return
                                           (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                              (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                         with
                                         | pair a3 b3 =>
                                             (fun (genv : global_env) (res : dvalue) =>
                                                @pair InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                  (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))) (lift_MemState ms)
                                                  (@pair MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)) sid
                                                     (@pair (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)
                                                        (@pair InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack (lift_local_env lenv) (lift_stack s))
                                                        (@pair InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue (lift_global_env genv) (fin_to_inf_dvalue res))))) a3 b3
                                         end) a2 b2
                                  end) a1 b1
                           end) a0 b0
                    end) a b
             end) r
    | TauF t =>
        (fun t0 : itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue)))) =>
           @go InfLP.Events.L3
             (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
             (@TauF InfLP.Events.L3
                (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                (itree InfLP.Events.L3
                   (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                (get_inf_tree t0))) t
    | VisF X e k =>
        (fun (X0 : Type) (e0 : L3 X0) (k0 : forall _ : X0, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) =>
           let X1 :
             itree InfLP.Events.L3
               (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
             match
               e0
               return
               (itree InfLP.Events.L3
                  (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
             with
             | inl1 x =>
                 (fun H : ExternalCallE X0 =>
                    (fun H0 : ExternalCallE X0 =>
                       let X1 :
                         forall _ : @eq Type X0 X0,
                           itree InfLP.Events.L3
                             (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                         match
                           H0 in (ExternalCallE T)
                           return
                           (forall _ : @eq Type T X0,
                               itree InfLP.Events.L3
                                 (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                    (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                         with
                         | ExternalCall t f args =>
                             (fun (t0 : dtyp) (f0 : uvalue) (args0 : list dvalue) (H1 : @eq Type dvalue X0) =>
                                (fun H2 : @eq Type dvalue X0 =>
                                   let H3 : @eq Type dvalue X0 := H2 in
                                   @eq_rect Type dvalue
                                     (fun _ : Type =>
                                        forall (_ : dtyp) (_ : uvalue) (_ : list dvalue),
                                          itree InfLP.Events.L3
                                            (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                               (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                     (fun (t1 : dtyp) (f1 : uvalue) (args1 : list dvalue) =>
                                        @eq_rect Type dvalue
                                          (fun X1 : Type =>
                                             forall (_ : forall _ : X1, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : ExternalCallE X1),
                                               itree InfLP.Events.L3
                                                 (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                    (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                          (fun (k1 : forall _ : dvalue, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : ExternalCallE dvalue) =>
                                             @go InfLP.Events.L3
                                               (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                  (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                               (@VisF InfLP.Events.L3
                                                  (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                     (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                                  (itree InfLP.Events.L3
                                                     (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                        (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))) E1.DV.dvalue
                                                  (@subevent E1.ExternalCallE InfLP.Events.L3
                                                     (@ReSum_inl (forall _ : Type, Type) IFun sum1 Cat_IFun Inl_sum1 E1.ExternalCallE InfLP.Events.ExternalCallE (sum1 InfLP.Events.PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) (@ReSum_id (forall _ : Type, Type) IFun Id_IFun InfLP.Events.ExternalCallE)) E1.DV.dvalue
                                                     (E1.ExternalCall t1 (fin_to_inf_uvalue f1) (@map LLVMParams64BitIntptr.Events.DV.dvalue LLVMParamsBigIntptr.Events.DV.dvalue fin_to_inf_dvalue args1)))
                                                  (fun x0 : E1.DV.dvalue =>
                                                     get_inf_tree
                                                       (let H5 : OOM DVCInfFin.DV2.dvalue := DVCInfFin.dvalue_convert_strict x0 in
                                                        match H5 return (itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) with
                                                        | NoOom a => (fun d : DVCInfFin.DV2.dvalue => k1 d) a
                                                        | Oom s =>
                                                            (fun s0 : string =>
                                                               @raiseOOM L3
                                                                 (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 OOME (sum1 PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) ExternalCallE
                                                                    (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 OOME (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) PickUvalueE
                                                                       (@ReSum_inl (forall _ : Type, Type) IFun sum1 Cat_IFun Inl_sum1 OOME OOME (sum1 UBE (sum1 DebugE FailureE)) (@ReSum_id (forall _ : Type, Type) IFun Id_IFun OOME))))
                                                                 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue)))) s0) s
                                                        end)))) X0 H2 k0 H0) X0 H3) H1 t0 f0 args0) t f args
                         end in
                           X1 (@eq_refl Type X0)) H) x
             | inr1 x =>
                 (fun X1 : sum1 PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) X0 =>
                    (fun X2 : sum1 PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) X0 =>
                       let X3 :
                         itree InfLP.Events.L3
                           (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                         match
                           X2
                           return
                           (itree InfLP.Events.L3
                              (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                 (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                         with
                         | inl1 x0 =>
                             (fun X3 : PickUvalueE X0 =>
                                (fun X4 : PickUvalueE X0 =>
                                   let X5 :
                                     forall _ : @eq Type X0 X0,
                                       itree InfLP.Events.L3
                                         (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                            (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                                     match
                                       X4 in (PickE T)
                                       return
                                       (forall _ : @eq Type T X0,
                                           itree InfLP.Events.L3
                                             (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                     with
                                     | pick Pre x1 =>
                                         (fun (Pre0 : Prop) (x2 : uvalue) (H : @eq Type (@sig dvalue (fun _ : dvalue => True)) X0) =>
                                            (fun H0 : @eq Type (@sig dvalue (fun _ : dvalue => True)) X0 =>
                                               let H1 : @eq Type (@sig dvalue (fun _ : dvalue => True)) X0 := H0 in
                                               @eq_rect Type (@sig dvalue (fun _ : dvalue => True))
                                                 (fun _ : Type =>
                                                    forall (_ : Prop) (_ : uvalue),
                                                      itree InfLP.Events.L3
                                                        (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                           (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                 (fun (Pre1 : Prop) (x3 : uvalue) =>
                                                    @eq_rect Type (@sig dvalue (fun _ : dvalue => True))
                                                      (fun X5 : Type =>
                                                         forall (_ : forall _ : X5, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : PickUvalueE X5),
                                                           itree InfLP.Events.L3
                                                             (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                      (fun (k1 : forall _ : @sig dvalue (fun _ : dvalue => True), itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : PickUvalueE (@sig dvalue (fun _ : dvalue => True))) =>
                                                         @go InfLP.Events.L3
                                                           (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                              (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                                           (@VisF InfLP.Events.L3
                                                              (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                 (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                                              (itree InfLP.Events.L3
                                                                 (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                    (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                              (@sig InfLP.Events.DV.dvalue (fun _ : InfLP.Events.DV.dvalue => True))
                                                              (@subevent (@E1.PickE LLVMParamsBigIntptr.Events.DV.uvalue InfLP.Events.DV.dvalue (fun (_ : InfLP.Events.DV.uvalue) (_ : InfLP.Events.DV.dvalue) => True)) InfLP.Events.L3
                                                                 (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 (@E1.PickE LLVMParamsBigIntptr.Events.DV.uvalue InfLP.Events.DV.dvalue (fun (_ : InfLP.Events.DV.uvalue) (_ : InfLP.Events.DV.dvalue) => True))
                                                                    (sum1 InfLP.Events.PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) InfLP.Events.ExternalCallE
                                                                    (@ReSum_inl (forall _ : Type, Type) IFun sum1 Cat_IFun Inl_sum1 (@E1.PickE LLVMParamsBigIntptr.Events.DV.uvalue InfLP.Events.DV.dvalue (fun (_ : InfLP.Events.DV.uvalue) (_ : InfLP.Events.DV.dvalue) => True)) InfLP.Events.PickUvalueE
                                                                       (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) (@ReSum_id (forall _ : Type, Type) IFun Id_IFun InfLP.Events.PickUvalueE))) (@sig InfLP.Events.DV.dvalue (fun _ : InfLP.Events.DV.dvalue => True))
                                                                 (@E1.pick LLVMParamsBigIntptr.Events.DV.uvalue InfLP.Events.DV.dvalue (fun (_ : InfLP.Events.DV.uvalue) (_ : InfLP.Events.DV.dvalue) => True) Pre1 (fin_to_inf_uvalue x3)))
                                                              (fun res : @sig InfLP.Events.DV.dvalue (fun _ : InfLP.Events.DV.dvalue => True) =>
                                                                 match
                                                                   res
                                                                   return
                                                                   (itree InfLP.Events.L3
                                                                      (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                         (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                                 with
                                                                 | @exist _ _ x4 p =>
                                                                     (fun (x5 : InfLP.Events.DV.dvalue) (t : True) =>
                                                                        get_inf_tree
                                                                          (let H2 : OOM DVCInfFin.DV2.dvalue := DVCInfFin.dvalue_convert_strict x5 in
                                                                           match H2 return (itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) with
                                                                           | NoOom a => (fun d : DVCInfFin.DV2.dvalue => k1 (@exist dvalue (fun _ : dvalue => True) d t)) a
                                                                           | Oom s =>
                                                                               (fun s0 : string =>
                                                                                  @raiseOOM L3
                                                                                    (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 OOME (sum1 PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) ExternalCallE
                                                                                       (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 OOME (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) PickUvalueE
                                                                                          (@ReSum_inl (forall _ : Type, Type) IFun sum1 Cat_IFun Inl_sum1 OOME OOME (sum1 UBE (sum1 DebugE FailureE)) (@ReSum_id (forall _ : Type, Type) IFun Id_IFun OOME))))
                                                                                    (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue)))) s0) s
                                                                           end)) x4 p
                                                                 end))) X0 H0 k0 X4) X0 H1) H Pre0 x2) Pre x1
                                     end in
                                       X5 (@eq_refl Type X0)) X3) x0
                         | inr1 x0 =>
                             (fun H : sum1 OOME (sum1 UBE (sum1 DebugE FailureE)) X0 =>
                                (fun H0 : sum1 OOME (sum1 UBE (sum1 DebugE FailureE)) X0 =>
                                   let X3 :
                                     itree InfLP.Events.L3
                                       (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                          (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                                     match
                                       H0
                                       return
                                       (itree InfLP.Events.L3
                                          (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                             (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                     with
                                     | inl1 x1 =>
                                         (fun H1 : OOME X0 =>
                                            (fun H2 : OOME X0 =>
                                               let X3 :
                                                 forall _ : @eq Type X0 X0,
                                                   itree InfLP.Events.L3
                                                     (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                        (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                                                 match
                                                   H2 in (OOME T)
                                                   return
                                                   (forall _ : @eq Type T X0,
                                                       itree InfLP.Events.L3
                                                         (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                            (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                 with
                                                 | ThrowOOM x2 =>
                                                     (fun (H3 : string) (H4 : @eq Type Empty_set X0) =>
                                                        (fun H5 : @eq Type Empty_set X0 =>
                                                           let H6 : @eq Type Empty_set X0 := H5 in
                                                           @eq_rect Type Empty_set
                                                             (fun _ : Type =>
                                                                forall _ : string,
                                                                  itree InfLP.Events.L3
                                                                    (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                       (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                             (fun H7 : string =>
                                                                @eq_rect Type Empty_set
                                                                  (fun X3 : Type =>
                                                                     forall (_ : forall _ : X3, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : OOME X3),
                                                                       itree InfLP.Events.L3
                                                                         (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                            (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                                  (fun (_ : forall _ : Empty_set, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : OOME Empty_set) =>
                                                                     @raiseOOM InfLP.Events.L3
                                                                       (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 OOME (sum1 InfLP.Events.PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) InfLP.Events.ExternalCallE
                                                                          (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 OOME (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) InfLP.Events.PickUvalueE
                                                                             (@ReSum_inl (forall _ : Type, Type) IFun sum1 Cat_IFun Inl_sum1 OOME OOME (sum1 UBE (sum1 DebugE FailureE)) (@ReSum_id (forall _ : Type, Type) IFun Id_IFun OOME))))
                                                                       (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                          (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) H7) X0 H5 k0 H2) X0 H6) H4 H3)
                                                       x2
                                                 end in
                                                   X3 (@eq_refl Type X0)) H1) x1
                                     | inr1 x1 =>
                                         (fun H1 : sum1 UBE (sum1 DebugE FailureE) X0 =>
                                            (fun H2 : sum1 UBE (sum1 DebugE FailureE) X0 =>
                                               let X3 :
                                                 itree InfLP.Events.L3
                                                   (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                      (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                                                 match
                                                   H2
                                                   return
                                                   (itree InfLP.Events.L3
                                                      (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                         (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                 with
                                                 | inl1 x2 =>
                                                     (fun H3 : UBE X0 =>
                                                        (fun H4 : UBE X0 =>
                                                           let X3 :
                                                             forall _ : @eq Type X0 X0,
                                                               itree InfLP.Events.L3
                                                                 (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                    (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                                                             match
                                                               H4 in (UBE T)
                                                               return
                                                               (forall _ : @eq Type T X0,
                                                                   itree InfLP.Events.L3
                                                                     (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                        (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                             with
                                                             | ThrowUB x3 =>
                                                                 (fun (H5 : string) (H6 : @eq Type Empty_set X0) =>
                                                                    (fun H7 : @eq Type Empty_set X0 =>
                                                                       let H8 : @eq Type Empty_set X0 := H7 in
                                                                       @eq_rect Type Empty_set
                                                                         (fun _ : Type =>
                                                                            forall _ : string,
                                                                              itree InfLP.Events.L3
                                                                                (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                   (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                                         (fun H9 : string =>
                                                                            @eq_rect Type Empty_set
                                                                              (fun X3 : Type =>
                                                                                 forall (_ : forall _ : X3, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : UBE X3),
                                                                                   itree InfLP.Events.L3
                                                                                     (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                        (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                                              (fun (_ : forall _ : Empty_set, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : UBE Empty_set) =>
                                                                                 @raiseUB InfLP.Events.L3
                                                                                   (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 UBE (sum1 InfLP.Events.PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) InfLP.Events.ExternalCallE
                                                                                      (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 UBE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) InfLP.Events.PickUvalueE
                                                                                         (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 UBE (sum1 UBE (sum1 DebugE FailureE)) OOME
                                                                                            (@ReSum_inl (forall _ : Type, Type) IFun sum1 Cat_IFun Inl_sum1 UBE UBE (sum1 DebugE FailureE) (@ReSum_id (forall _ : Type, Type) IFun Id_IFun UBE)))))
                                                                                   (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                      (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) H9) X0 H7 k0 H4) X0 H8)
                                                                      H6 H5) x3
                                                             end in
                                                               X3 (@eq_refl Type X0)) H3) x2
                                                 | inr1 x2 =>
                                                     (fun H3 : sum1 DebugE FailureE X0 =>
                                                        (fun H4 : sum1 DebugE FailureE X0 =>
                                                           let X3 :
                                                             itree InfLP.Events.L3
                                                               (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                  (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                                                             match
                                                               H4
                                                               return
                                                               (itree InfLP.Events.L3
                                                                  (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                     (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                             with
                                                             | inl1 x3 =>
                                                                 (fun H5 : DebugE X0 =>
                                                                    (fun H6 : DebugE X0 =>
                                                                       let X3 :
                                                                         forall _ : @eq Type X0 X0,
                                                                           itree InfLP.Events.L3
                                                                             (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                                                                         match
                                                                           H6 in (DebugE T)
                                                                           return
                                                                           (forall _ : @eq Type T X0,
                                                                               itree InfLP.Events.L3
                                                                                 (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                    (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                                         with
                                                                         | Debug x4 =>
                                                                             (fun (H7 : string) (H8 : @eq Type unit X0) =>
                                                                                (fun H9 : @eq Type unit X0 =>
                                                                                   let H10 : @eq Type unit X0 := H9 in
                                                                                   @eq_rect Type unit
                                                                                     (fun _ : Type =>
                                                                                        forall _ : string,
                                                                                          itree InfLP.Events.L3
                                                                                            (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                               (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                                                     (fun H11 : string =>
                                                                                        @eq_rect Type unit
                                                                                          (fun X3 : Type =>
                                                                                             forall (_ : forall _ : X3, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : DebugE X3),
                                                                                               itree InfLP.Events.L3
                                                                                                 (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                                    (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                                                          (fun (k1 : forall _ : unit, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : DebugE unit) =>
                                                                                             @go InfLP.Events.L3
                                                                                               (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                                  (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                                                                               (@VisF InfLP.Events.L3
                                                                                                  (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                                     (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                                                                                  (itree InfLP.Events.L3
                                                                                                     (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                                        (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))) unit
                                                                                                  (@subevent DebugE InfLP.Events.L3
                                                                                                     (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 DebugE (sum1 InfLP.Events.PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) InfLP.Events.ExternalCallE
                                                                                                        (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 DebugE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) InfLP.Events.PickUvalueE
                                                                                                           (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 DebugE (sum1 UBE (sum1 DebugE FailureE)) OOME
                                                                                                              (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 DebugE (sum1 DebugE FailureE) UBE
                                                                                                                 (@ReSum_inl (forall _ : Type, Type) IFun sum1 Cat_IFun Inl_sum1 DebugE DebugE FailureE (@ReSum_id (forall _ : Type, Type) IFun Id_IFun DebugE)))))) unit (Debug H11)) (fun H13 : unit => get_inf_tree (k1 H13)))) X0 H9 k0 H6) X0 H10) H8 H7) x4
                                                                         end in
                                                                           X3 (@eq_refl Type X0)) H5) x3
                                                             | inr1 x3 =>
                                                                 (fun H5 : FailureE X0 =>
                                                                    (fun H6 : FailureE X0 =>
                                                                       let X3 :
                                                                         forall _ : @eq Type X0 X0,
                                                                           itree InfLP.Events.L3
                                                                             (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))) :=
                                                                         match
                                                                           H6 in (FailureE T)
                                                                           return
                                                                           (forall _ : @eq Type T X0,
                                                                               itree InfLP.Events.L3
                                                                                 (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                    (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                                         with
                                                                         | Throw x4 =>
                                                                             (fun (H7 : string) (H8 : @eq Type Empty_set X0) =>
                                                                                (fun H9 : @eq Type Empty_set X0 =>
                                                                                   let H10 : @eq Type Empty_set X0 := H9 in
                                                                                   @eq_rect Type Empty_set
                                                                                     (fun _ : Type =>
                                                                                        forall _ : string,
                                                                                          itree InfLP.Events.L3
                                                                                            (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                               (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                                                     (fun H11 : string =>
                                                                                        @eq_rect Type Empty_set
                                                                                          (fun X3 : Type =>
                                                                                             forall (_ : forall _ : X3, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : FailureE X3),
                                                                                               itree InfLP.Events.L3
                                                                                                 (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                                    (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue)))))
                                                                                          (fun (_ : forall _ : Empty_set, itree L3 (prod FinMem.MMEP.MMSP.MemState (prod MemPropT.store_id (prod (prod local_env (@stack local_env)) (prod global_env dvalue))))) (_ : FailureE Empty_set) =>
                                                                                             @LLVMEvents.raise InfLP.Events.L3
                                                                                               (prod InterpreterStackBigIntptr.LLVM.MEM.MMEP.MMSP.MemState
                                                                                                  (prod MemPropT.store_id (prod (prod InterpreterStackBigIntptr.LLVM.Local.local_env InterpreterStackBigIntptr.LLVM.Stack.lstack) (prod InterpreterStackBigIntptr.LLVM.Global.global_env InterpreterStackBigIntptr.LP.Events.DV.dvalue))))
                                                                                               (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 FailureE (sum1 InfLP.Events.PickUvalueE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE)))) InfLP.Events.ExternalCallE
                                                                                                  (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 FailureE (sum1 OOME (sum1 UBE (sum1 DebugE FailureE))) InfLP.Events.PickUvalueE
                                                                                                     (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 FailureE (sum1 UBE (sum1 DebugE FailureE)) OOME
                                                                                                        (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 FailureE (sum1 DebugE FailureE) UBE
                                                                                                           (@ReSum_inr (forall _ : Type, Type) IFun sum1 Cat_IFun Inr_sum1 FailureE FailureE DebugE (@ReSum_id (forall _ : Type, Type) IFun Id_IFun FailureE)))))) H11) X0 H9 k0 H6) X0 H10) H8 H7) x4
                                                                         end in
                                                                           X3 (@eq_refl Type X0)) H5) x3
                                                             end in
                                                           X3) H3) x2
                                                 end in
                                               X3) H1) x1
                                     end in
                                   X3) H) x0
                         end in
                       X3) X1) x
             end in
           X1) X e k
    end.

  Require Import ITree.Eq.EuttExtras.

  Lemma paco2_eq_itree_refl : forall E R r (t : itree E R), paco2 (eqit_ eq false false id) r t t.
  Proof.
    intros. eapply paco2_mon with (r := bot2); intuition.
    enough (t ≅ t); auto. reflexivity.
  Qed.


  Lemma fin_inf_ptoi :
    forall a a',
      InfToFinAddrConvert.addr_convert a' = NoOom a ->
      LLVMParams64BitIntptr.PTOI.ptr_to_int a = LLVMParamsBigIntptr.PTOI.ptr_to_int a'.
  Proof.
  Admitted.

  Lemma fin_inf_from_Z :
    forall ip_f z,
      LLVMParams64BitIntptr.IP.from_Z z = NoOom ip_f ->
      exists ip_i,
        LLVMParamsBigIntptr.IP.from_Z z = NoOom ip_i.
  Proof.
  Admitted.

  (* TODO: Move this and use it in picky intptr reasoning admits *)
  Lemma fin_inf_from_Z_to_Z :
    forall z x y,
      LLVMParamsBigIntptr.IP.from_Z z = NoOom x ->
      LLVMParams64BitIntptr.IP.from_Z z = NoOom y ->
      LLVMParams64BitIntptr.IP.to_Z y = LLVMParamsBigIntptr.IP.to_Z x.
  Proof.
    intros z x y ZX ZY.
    pose proof BigIP.from_Z_to_Z z x ZX.
    pose proof IP.from_Z_to_Z z y ZY.
    rewrite H, H0.
    auto.
  Qed.


    (* TODO: Move this *)
  Lemma fin_to_inf_addr_ptr_to_int :
    forall ptr,
      LLVMParamsBigIntptr.PTOI.ptr_to_int (fin_to_inf_addr ptr) = LLVMParams64BitIntptr.PTOI.ptr_to_int ptr.
  Proof.
    intros ptr.
    destruct ptr.
    unfold fin_to_inf_addr.
    break_match_goal.
    erewrite fin_inf_ptoi; eauto.
    apply FinToInfAddrConvertSafe.addr_convert_safe; auto.
  Qed.

  (* TODO: Move this *)
  Lemma ptr_in_frame_prop_lift :
    forall f ptr,
      FinMem.MMEP.MMSP.ptr_in_frame_prop f ptr ->
      InfMem.MMEP.MMSP.ptr_in_frame_prop (lift_Frame f) (fin_to_inf_addr ptr).
  Proof.
    intros f ptr IN.
    red in *.
    unfold lift_Frame.
    rewrite List.map_map.
    rewrite fin_to_inf_addr_ptr_to_int.
    replace (fun x : FinAddr.addr => LLVMParamsBigIntptr.PTOI.ptr_to_int (fin_to_inf_addr x)) with
      (fun x : FinAddr.addr => LLVMParams64BitIntptr.PTOI.ptr_to_int x).
    apply IN.

    apply Axioms.functional_extensionality.
    intros x.
    rewrite fin_to_inf_addr_ptr_to_int.
    auto.
  Qed.

  (* TODO: Move this *)
  Lemma ptr_in_frame_prop_lift_inv :
    forall f ptr_inf,
      InfMem.MMEP.MMSP.ptr_in_frame_prop (lift_Frame f) ptr_inf ->
      exists ptr_fin,
        InfToFinAddrConvert.addr_convert ptr_inf = NoOom ptr_fin /\
          FinMem.MMEP.MMSP.ptr_in_frame_prop f ptr_fin.
  Proof.
    intros f ptr IN.
    red in IN.
    unfold lift_Frame in IN.
    rewrite List.map_map in IN.
    apply in_map_iff in IN.
    destruct IN as (?&?&?).
    rewrite fin_to_inf_addr_ptr_to_int in H.
    pose proof ITOP.int_to_ptr_ptr_to_int_exists x (InfPROV.address_provenance ptr).
    destruct H1 as (?&?&?&?).
    exists x0.
    split.
    - destruct ptr.
      cbn in *; subst; auto.
    - red.
      apply in_map_iff.
      exists x.
      split; auto.
  Qed.


  (* TODO: Move this to MMSP or something *)
  Lemma frame_eqv_empty_l :
    forall f,
      Memory64BitIntptr.MMEP.MMSP.frame_eqv [] f ->
      f = [].
  Proof.
    intros f EQV.
    destruct f; auto.
    red in  EQV.
    specialize (EQV a).
    destruct EQV.
    forward H0; cbn; auto.
    red in H0.
    cbn in H0.
    contradiction.
  Qed.

  (* TODO: Move this to MMSP or something *)
  Lemma frame_eqv_empty_r :
    forall f,
      Memory64BitIntptr.MMEP.MMSP.frame_eqv f [] ->
      f = [].
  Proof.
    intros f EQV.
    symmetry in EQV.
    apply frame_eqv_empty_l.
    auto.
  Qed.


  (* TODO: Move this *)
  Lemma fin_to_inf_addr_conv_inf :
    forall ptr_inf ptr_fin,
      InfToFinAddrConvert.addr_convert ptr_inf = NoOom ptr_fin ->
      fin_to_inf_addr ptr_fin = ptr_inf.
  Proof.
    intros ptr_inf ptr_fin CONV.
    unfold fin_to_inf_addr.
    break_match_goal.
    clear Heqs.
    apply FinToInfAddrConvertSafe.addr_convert_safe in e.
    eapply InfToFinAddrConvert.addr_convert_injective; eauto.
  Qed.


  (* TODO: Move this *)
  Lemma frame_stack_eqv_lift_inv :
    forall fs1 fs2,
      InfMem.MMEP.MMSP.frame_stack_eqv fs1 fs2 ->
      exists fs1_fin fs2_fin,
        fs1 = lift_FrameStack fs1_fin /\
          fs2 = lift_FrameStack fs2_fin /\
          FinMem.MMEP.MMSP.frame_stack_eqv fs1_fin fs2_fin.
  Proof.
    unfold InfMem.MMEP.MMSP.frame_stack_eqv.
    induction fs1.
    - destruct fs2; intros.
      + specialize (H f).


  Admitted.


  (* TODO: Move this *)
  Lemma frame_eqv_lift :
    forall f1 f2,
      FinMem.MMEP.MMSP.frame_eqv f1 f2 ->
      InfMem.MMEP.MMSP.frame_eqv (lift_Frame f1) (lift_Frame f2).
  Proof.
    intros f1 f2 EQV.
    red in EQV; red.

    intros ptr.
    split; intros IN.
    - apply ptr_in_frame_prop_lift_inv in IN.
      destruct IN as (ptr_fin & CONV & IN).
      apply EQV in IN.
      apply ptr_in_frame_prop_lift in IN.
      erewrite fin_to_inf_addr_conv_inf in IN; eauto.
    - apply ptr_in_frame_prop_lift_inv in IN.
      destruct IN as (ptr_fin & CONV & IN).
      apply EQV in IN.
      apply ptr_in_frame_prop_lift in IN.
      erewrite fin_to_inf_addr_conv_inf in IN; eauto.
  Qed.

  (* TODO: Move this *)
  Lemma FSNth_eqv_lift :
    forall n fs f,
      FinMem.MMEP.MMSP.FSNth_eqv fs n f ->
      InfMem.MMEP.MMSP.FSNth_eqv (lift_FrameStack fs) n (lift_Frame f).
  Proof.
    induction n; intros fs f NTHEQV.
    - destruct fs; cbn in *;
        apply frame_eqv_lift; auto.
    - destruct fs; cbn in *; auto.
  Qed.

  (* TODO: Move this *)
  Lemma lift_FrameStack_snoc :
    forall fs f,
      lift_FrameStack (FinMemMMSP.Snoc fs f) = InfMemMMSP.Snoc (lift_FrameStack fs) (lift_Frame f).
  Proof.
    induction fs; intros f_fin; cbn; auto.
  Qed.

  (* TODO: Move this *)
  Lemma FSNth_eqv_lift_inv :
    forall n fs f,
      InfMem.MMEP.MMSP.FSNth_eqv (lift_FrameStack fs) n f ->
      exists f_fin,
        InfMem.MMEP.MMSP.frame_eqv (lift_Frame f_fin) f /\
          FinMem.MMEP.MMSP.FSNth_eqv fs n f_fin.
  Proof.
    induction n; intros fs f NTHEQV.
    - destruct fs; cbn in *; exists f0;
        split; auto; reflexivity.
    - destruct fs.
      cbn in *; contradiction.

      rewrite lift_FrameStack_snoc in NTHEQV.
      cbn in *.
      eauto.
  Qed.

  (* TODO: Move this *)
  Lemma FSNth_frame_eqv :
    forall n fs f1 f2,
      InfMem.MMEP.MMSP.frame_eqv f1 f2 ->
      InfMem.MMEP.MMSP.FSNth_eqv fs n f1 ->
      InfMem.MMEP.MMSP.FSNth_eqv fs n f2.
  Proof.
    induction n;
      intros fs f1 f2 EQV NTHEQV.
    - destruct fs; cbn in *;
        rewrite NTHEQV; auto.
    - destruct fs; cbn in *; eauto.
  Qed.


  (* TODO: Move this *)
  #[global] Instance FSNth_eqv_Proper :
    Proper (InfMem.MMEP.MMSP.frame_stack_eqv ==> eq ==> InfMem.MMEP.MMSP.frame_eqv ==> iff) InfMem.MMEP.MMSP.FSNth_eqv.
  Proof.
    unfold Proper, respectful.
    intros x y H x0 y0 H0 x1 y1 H1; subst.
    split; intros NTH.
    - red in H.
      apply H.
      eapply FSNth_frame_eqv; eauto.
    - red in H.
      apply H.
      eapply FSNth_frame_eqv; eauto.
      symmetry; auto.
  Qed.


  (* TODO: Move this *)
  Lemma frame_stack_eqv_lift :
    forall fs1 fs2,
      FinMem.MMEP.MMSP.frame_stack_eqv fs1 fs2 ->
      InfMem.MMEP.MMSP.frame_stack_eqv (lift_FrameStack fs1) (lift_FrameStack fs2).
  Proof.
    intros fs1 fs2 EQV.
    red in *.
    intros f n.
    split; intros FSE.
    - apply FSNth_eqv_lift_inv in FSE.
      destruct FSE as (f_fin & F & FSE).

      rewrite <- F.
      apply FSNth_eqv_lift.
      apply EQV.
      auto.
    - apply FSNth_eqv_lift_inv in FSE.
      destruct FSE as (f_fin & F & FSE).

      rewrite <- F.
      apply FSNth_eqv_lift.
      apply EQV.
      auto.
  Qed.




  Lemma get_inf_tree_equation :
    forall t_fin2,
      get_inf_tree t_fin2 ≅ _get_inf_tree (observe t_fin2).
  Proof.
    pcofix CIH.
    intros t_fin2.
    destruct (observe t_fin2) eqn:HTFIN.
    - rewrite (itree_eta_ t_fin2).
      rewrite HTFIN.
      cbn.
      pstep; red; cbn.
      constructor.
      reflexivity.
    - rewrite (itree_eta_ t_fin2).
      rewrite HTFIN.
      cbn.
      pstep; red; cbn.
      constructor.
      left.
      apply paco2_eq_itree_refl.
    - rewrite (itree_eta_ t_fin2).
      unfold _get_inf_tree.
      rewrite HTFIN.
      destruct e.
      admit.
      admit.
  Admitted.

  Lemma fin_to_inf_dvalue_refine_strict :
    forall d,
      DVC1.dvalue_refine_strict (fin_to_inf_dvalue d) d.
  Proof.
    intros d.
    rewrite DVC1.dvalue_refine_strict_equation.
    unfold fin_to_inf_dvalue.
    break_match; cbn in *.
    destruct p.
    auto.
  Qed.

  Lemma fin_to_inf_uvalue_refine_strict :
    forall u,
      DVC1.uvalue_refine_strict (fin_to_inf_uvalue u) u.
  Proof.
    intros u.
    rewrite DVC1.uvalue_refine_strict_equation.
    unfold fin_to_inf_uvalue.
    break_match; cbn in *.
    destruct p.
    auto.
  Qed.

  Import AListFacts.

  Lemma lift_local_env_refine_strict :
    forall l,
      local_refine_strict (lift_local_env l) l.
  Proof.
    induction l.
    - cbn.
      apply alist_refine_empty.
    - destruct a.
      apply alist_refine_cons; cbn; auto.
      apply fin_to_inf_uvalue_refine_strict.
  Qed.

  Lemma lift_stack_refine_strict :
    forall s,
      stack_refine_strict (lift_stack s) s.
  Proof.
    induction s.
    - cbn.
      apply stack_refine_strict_empty.
    - apply stack_refine_strict_add; auto.
      apply lift_local_env_refine_strict.
  Qed.

  Lemma lift_global_env_refine_strict :
    forall g,
      global_refine_strict (lift_global_env g) g.
  Proof.
    induction g.
    - cbn.
      apply alist_refine_empty.
    - destruct a.
      apply alist_refine_cons; cbn; auto.
      apply fin_to_inf_dvalue_refine_strict.
  Qed.

  Lemma convert_FrameStack_lift :
    forall fs,
      convert_FrameStack (lift_FrameStack fs) = NoOom fs.
  Proof.
  Admitted.

  Lemma convert_memory_lift :
    forall m,
      convert_memory (lift_memory m) = NoOom m.
  Proof.
  Admitted.

  Lemma convert_Heap_lift :
    forall h,
      convert_Heap (lift_Heap h) = NoOom h.
  Proof.
  Admitted.

  Lemma convert_memory_stack_lift :
    forall ms,
      convert_memory_stack (lift_memory_stack ms) = NoOom ms.
  Proof.
    induction ms.
    cbn.
    setoid_rewrite convert_memory_lift.
    setoid_rewrite convert_FrameStack_lift.
    setoid_rewrite convert_Heap_lift.
    reflexivity.
  Qed.

  Lemma lift_MemState_refine :
    forall ms,
      MemState_refine (lift_MemState ms) ms.
  Proof.
    intros ms.
    red.
    destruct ms.
    cbn.
    rewrite convert_memory_stack_lift.
    auto.
  Qed.


  Lemma lift_MemState_refine_prop :
    forall ms,
      Heap_in_bounds ms ->
      MemState_refine_prop (lift_MemState ms) ms.
  Proof.
    intros ms HIB.
    red.
    destruct ms.
    cbn.
    repeat split; intros; cbn in * ; try reflexivity; try intuition;
      try red in H; try (rewrite <- H; auto); try (rewrite H; auto).
  Qed.

  (* TODO: Move this... *)
  Lemma MemPropT_bind_ret_inv :
    forall {S A B}
      (ma : MemPropT S A)
      (mab : A -> MemPropT S B)
      {s1 s2 b}
      (M :
        (a <- ma;;
         mab a) s1 (ret (s2, b))),
    exists s' a, ma s1 (ret (s', a)) /\ mab a s' (ret (s2, b)).
  Proof.
    intros S A B ma mab s1 s2 b M.
    auto.
  Qed.

  (* This might be a good idea, should make the proofs more modular... *)
  (* TODO: Move this *)
  Lemma MemPropT_fin_inf_bind :
    forall {ms_inf_start : MemoryBigIntptr.MMEP.MMSP.MemState}
      {ms_fin_start ms_fin_final : Memory64BitIntptr.MMEP.MMSP.MemState}
      {A_FIN A_INF B_FIN B_INF}
      (ma_fin : MemPropT Memory64BitIntptr.MMEP.MMSP.MemState A_FIN)
      {ma_inf : MemPropT MemoryBigIntptr.MMEP.MMSP.MemState A_INF}
      {mab_fin : A_FIN -> MemPropT Memory64BitIntptr.MMEP.MMSP.MemState B_FIN}
      {mab_inf : A_INF -> MemPropT MemoryBigIntptr.MMEP.MMSP.MemState B_INF}
      {res_fin}

      (A_REF : A_INF -> A_FIN -> Prop)
      (B_REF : B_INF -> B_FIN -> Prop)

      (MEM_REF_START : MemState_refine_prop ms_inf_start ms_fin_start)

      (* Not sure about quantification *)
      (MA: forall a_fin ms_fin_ma,
          ma_fin ms_fin_start (ret (ms_fin_ma, a_fin)) ->
          exists a_inf ms_inf_ma,
            ma_inf ms_inf_start (ret (ms_inf_ma, a_inf)) /\
              A_REF a_inf a_fin /\
              MemState_refine_prop ms_inf_ma ms_fin_ma)

      (* Not sure about quantification *)
      (K: forall ms_inf ms_fin ms_fin' a_fin a_inf b_fin,
          A_REF a_inf a_fin ->
          MemState_refine_prop ms_inf ms_fin ->
          mab_fin a_fin ms_fin (ret (ms_fin', b_fin)) ->
          exists b_inf ms_inf',
            mab_inf a_inf ms_inf (ret (ms_inf', b_inf)) /\
              B_REF b_inf b_fin /\
              MemState_refine_prop ms_inf' ms_fin')

      (FIN: (a <- ma_fin;;
             mab_fin a) ms_fin_start (ret (ms_fin_final, res_fin))),

    exists res_inf ms_inf_final,
      (a <- ma_inf;;
       mab_inf a) ms_inf_start (ret (ms_inf_final, res_inf)) /\
        B_REF res_inf res_fin /\
        MemState_refine_prop ms_inf_final ms_fin_final.
  Proof.
    intros ms_inf_start ms_fin_start ms_fin_final A_FIN A_INF B_FIN B_INF ma_fin ma_inf mab_fin mab_inf res_fin A_REF B_REF MEM_REF_START MA K FIN.

    repeat red in FIN.
    destruct FIN as (sab&a&FIN&FIN_AB).

    apply MA in FIN as (a_inf&ms_inf''&INF&A&MSR).
    eapply K in FIN_AB; eauto.

    destruct FIN_AB as (res_inf & ms_inf_final & MAB_INF & RES_REF & MEM_RES_FINAL).

    exists res_inf. exists ms_inf_final.
    split; auto.

    repeat red.
    exists ms_inf''.
    exists a_inf.
    split; auto.
  Qed.

  Lemma MemPropT_fin_inf_map_monad :
    forall {A_INF A_FIN B_INF B_FIN}
      {l_inf : list A_INF} {l_fin : list A_FIN}
      {f_fin : A_FIN -> MemPropT Memory64BitIntptr.MMEP.MMSP.MemState B_FIN} {f_inf : A_INF -> MemPropT MemoryBigIntptr.MMEP.MMSP.MemState B_INF}
      {ms_fin_start ms_fin_final : Memory64BitIntptr.MMEP.MMSP.MemState}
      {ms_inf_start : MemoryBigIntptr.MMEP.MMSP.MemState}
      {res_fin : list B_FIN}

      (A_REF : A_INF -> A_FIN -> Prop)
      (B_REF : B_INF -> B_FIN -> Prop)

      (MEM_REF_START : MemState_refine_prop ms_inf_start ms_fin_start)

      (F : forall a_fin a_inf b_fin ms_fin ms_inf ms_fin_ma,
          MemState_refine_prop ms_inf ms_fin ->
          A_REF a_inf a_fin ->
          f_fin a_fin ms_fin (ret (ms_fin_ma, b_fin)) ->
          exists b_inf ms_inf_ma,
            f_inf a_inf ms_inf (ret (ms_inf_ma, b_inf)) /\
              B_REF b_inf b_fin /\
              MemState_refine_prop ms_inf_ma ms_fin_ma)

      (AS : Forall2 A_REF l_inf l_fin)
      (FIN : map_monad f_fin l_fin ms_fin_start (ret (ms_fin_final, res_fin))),

    exists res_inf ms_inf_final,
      map_monad f_inf l_inf ms_inf_start (ret (ms_inf_final, res_inf)) /\
        Forall2 B_REF res_inf res_fin /\
        MemState_refine_prop ms_inf_final ms_fin_final.
  Proof.
    intros A_INF A_FIN B_INF B_FIN l_inf l_fin f_fin f_inf ms_fin_start ms_fin_final ms_inf_start res_fin A_REF
      B_REF MEM_REF_START F AS FIN.

    generalize dependent res_fin.
    generalize dependent ms_fin_start.
    generalize dependent ms_inf_start.
    induction AS; intros ms_inf_start ms_fin_start MEM_REF_START res_fin FIN.
    - cbn. exists []. exists ms_inf_start.
      cbn in FIN.
      destruct FIN; subst.

      split; auto.
    - rewrite map_monad_unfold in FIN.
      apply MemPropT_bind_ret_inv in FIN as (ms_fin' & b_fin & F_Y & FIN).
      apply MemPropT_bind_ret_inv in FIN as (ms_fin_final' & b_fin_rest & MAP_FIN & RET_FIN).
      cbn in RET_FIN.
      destruct RET_FIN; subst.

      pose proof (F _ _ _ _ _ _ MEM_REF_START H F_Y) as (b_inf & ms_inf' & F_X & B & MSR).
      specialize (IHAS ms_inf' ms_fin' MSR _ MAP_FIN) as (b_inf_rest & ms_inf_final' & MAP_INF & B_ALL & MSR_FINAL).

      exists (b_inf :: b_inf_rest).
      exists ms_inf_final'.
      split; auto.

      rewrite map_monad_unfold.

      repeat red.
      do 2 eexists.
      split; eauto.
      do 2 eexists.
      split; eauto.

      cbn.
      auto.
  Qed.

  Lemma get_inf_tree_rutt :
    forall t,
      orutt (OOM:=OOME) L3_refine_strict L3_res_refine_strict
        (MemState_refine
           × (eq
                × (local_refine_strict × stack_refine_strict
                     × (global_refine_strict × DVC1.dvalue_refine_strict)))) (get_inf_tree t) t.
  Proof.
    intros t.
    rewrite (itree_eta_ t).
    genobs t ot.
    clear t Heqot.
    revert ot.
    pcofix CIH.
    intros ot.

    induction ot.
    - (* Ret *)
      pstep; red; cbn.
      constructor.
      destruct r0.
      repeat destruct p.
      destruct p0.
      repeat constructor; cbn.
      + apply lift_MemState_refine.
      + apply lift_local_env_refine_strict.
      + apply lift_stack_refine_strict.
      + apply lift_global_env_refine_strict.
      + apply fin_to_inf_dvalue_refine_strict.
    - (* Tau *)
      pstep; red; cbn.
      constructor.
      right.
      rewrite (itree_eta_ t).
      apply CIH.
    - (* Vis nodes *)
      destruct e.
      { (* ExternalCallE *)
        destruct e.
        pstep; red; cbn.

        constructor.
        { red. cbn.
          split; auto.
          split.
          apply fin_to_inf_uvalue_refine_strict.
          apply Util.Forall2_forall.
          split.
          apply map_length.

          intros i a b H H0.
          apply Nth_map_iff in H.
          destruct H. destruct H.
          subst.

          cbn in *.
          rewrite H1 in H0.
          inv H0.
          apply fin_to_inf_dvalue_refine_strict.
        }

        { intros a b [TT [F [ARGS AB]]].
          rewrite DVCInfFin.dvalue_refine_strict_equation in AB.
          rewrite AB.
          rewrite (itree_eta_ (k b)).
          right.
          apply CIH.
        }

        { intros o CONTRA; inv CONTRA.
        }
      }

      destruct s.
      { (* PickUvalue *)
        destruct p.
        pstep; red; cbn.

        constructor.
        { red. cbn.
          split; [tauto|].
          apply fin_to_inf_uvalue_refine_strict.
        }

        { intros [a []] [b []] [_ [X AB]].
          rewrite DVCInfFin.dvalue_refine_strict_equation in AB.
          rewrite AB.
          rewrite (itree_eta_ (k _)).
          right.
          apply CIH.
        }

        { intros o CONTRA; inv CONTRA.
        }
      }

      destruct s.
      { (* OOM *)
        destruct o.
        pstep; red; cbn.

        change (inr1 (inr1 (inl1 (ThrowOOM s)))) with (@subevent _ _ (ReSum_inr IFun sum1 OOME
                                                                        (PickUvalueE +' OOME +' UBE +' DebugE +' FailureE)
                                                                        ExternalCallE) _ (ThrowOOM s)).

        apply EqVisOOM.
      }

      destruct s.
      { (* UBE *)
        destruct u.
        pstep; red; cbn.

        constructor.
        { cbn; auto.
        }

        { intros [] [] _.
        }

        { intros o CONTRA; inv CONTRA.
        }
      }

      destruct s.
      { (* DebugE *)
        destruct d.
        pstep; red; cbn.

        constructor.
        { cbn; auto.
        }

        { intros [] [] _.
          rewrite (itree_eta_ (k _)).
          right.
          apply CIH.
        }

        { intros o CONTRA; inv CONTRA.
        }
      }

      { (* FailureE *)
        destruct f.
        pstep; red; cbn.

        constructor.
        { cbn; auto.
        }

        { intros [] [] _.
        }

        { intros o CONTRA; inv CONTRA.
        }
      }
  Qed.

  Import InterpMemoryProp.

  #[global] Instance get_inf_tree_Proper :
    Proper (eutt eq ==> eutt eq) get_inf_tree.
  Proof.
    unfold Proper, respectful.
    intros x y EQ.
    rewrite (itree_eta_ x) in *.
    rewrite (itree_eta_ y) in *.
    genobs x ox.
    genobs y oy.
    clear x Heqox y Heqoy.
    revert ox oy EQ.
    pcofix CIH.
    intros ox oy EQ.
    punfold EQ. red in EQ. cbn in EQ.
    dependent induction EQ.
    - (* Ret Ret *)
      subst.
      pstep; red; cbn.
      constructor; auto.
    - (* Tau Tau *)
      pstep; red; cbn.
      constructor.
      right.
      rewrite (itree_eta_ m1).
      rewrite (itree_eta_ m2).
      eapply CIH.
      pclearbot.
      repeat rewrite <- itree_eta_.
      apply REL.
    - (* Vis Vis *)
      destruct e.

      { (* ExternalCallE *)
        destruct e.
        pstep; red; cbn.
        constructor.
        intros v.
        red.
        right.
        rewrite (itree_eta_
                   match DVCInfFin.dvalue_convert_strict v with
                   | NoOom a => k1 a
                   | Oom s => raiseOOM s
                   end).
        rewrite (itree_eta_
                   match DVCInfFin.dvalue_convert_strict v with
                   | NoOom a => k2 a
                   | Oom s => raiseOOM s
                   end).
        apply CIH.
        repeat rewrite <- itree_eta_.
        break_match; [|reflexivity].
        specialize (REL d).
        red in REL.
        pclearbot.
        eauto.
      }

      destruct s.
      { (* PickUvalueE *)
        destruct p.
        pstep; red; cbn.
        constructor.
        intros [v []].
        red.
        right.
        match goal with
        | H: _ |- r (get_inf_tree ?t1) (get_inf_tree ?t2) =>
            rewrite (itree_eta_ t1);
            rewrite (itree_eta_ t2)
        end.
        apply CIH.
        repeat rewrite <- itree_eta_.
        break_match; [|reflexivity].
        specialize (REL (exist _ d I)).
        red in REL.
        pclearbot.
        eauto.
      }

      destruct s.
      { (* OOME *)
        destruct o.
        pstep; red; cbn.
        constructor.
        intros [] _.
      }

      destruct s.
      { (* UBE *)
        destruct u0.
        pstep; red; cbn.
        constructor.
        intros [] _.
      }

      destruct s.
      { (* DebugE *)
        destruct d.
        pstep; red; cbn.
        constructor.
        intros [].
        red.
        right.
        match goal with
        | H: _ |- r (get_inf_tree ?t1) (get_inf_tree ?t2) =>
            rewrite (itree_eta_ t1);
            rewrite (itree_eta_ t2)
        end.
        apply CIH.
        repeat rewrite <- itree_eta_.
        specialize (REL tt).
        red in REL.
        pclearbot.
        eauto.
      }

      { (* FailureE *)
        destruct f.
        pstep; red; cbn.
        constructor.
        intros [] _.
      }
    - (* TauL *)
      pstep; red; cbn.
      constructor; auto.
      punfold IHEQ.
    - (* TauR *)
      pstep; red; cbn.
      constructor; auto.
      punfold IHEQ.
  Qed.

  (* TODO: not 100% sure what R, T1T2, pre, post should be / what constraints are needed for them *)
  Lemma oom_orutt :
    forall {E F T1 T2}
      `{OE : OOME -< E}
      `{OF : OOME -< F}
      (R : relation T1)
      (T1T2 : T1 -> T2 -> Prop)
      (pre : prerel E F)
      (post : postrel E F)
      (t_source t_oom : itree E T1) (t_final : itree F T2),
      refine_OOM_h R t_source t_oom ->
      orutt (OOM:=OOME) pre post T1T2 t_oom t_final ->
      orutt (OOM:=OOME) pre post T1T2 t_source t_final.
  Proof.
    intros E F T1 T2 OE OF R T1T2 pre post t_source t_oom t_final REF_OOM ORUTT.
  Admitted.

  (* TODO: inversion lemmas for dvalue_convert_strict *)
  Lemma dvalue_convert_strict_addr_inv :
    forall x a,
      DVCInfFin.dvalue_convert_strict x = NoOom (DVCInfFin.DV2.DVALUE_Addr a) ->
      exists a',
        InfToFinAddrConvert.addr_convert a' = NoOom a /\
          x = DVCInfFin.DV1.DVALUE_Addr a'.
  Proof.
    intros x a H.
    rewrite DVCInfFin.dvalue_convert_strict_equation in H.
    destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
    break_match_hyp; inv H1.
    exists a0; auto.
  Qed.

  Lemma dvalue_convert_strict_iptr_inv :
    forall x n,
      DVCInfFin.dvalue_convert_strict x = NoOom (DVCInfFin.DV2.DVALUE_IPTR n) ->
      exists n',
        IP.from_Z (InterpreterStackBigIntptr.LP.IP.to_Z n') = NoOom n /\
          x = DVCInfFin.DV1.DVALUE_IPTR n'.
  Proof.
    intros x n H.
    rewrite DVCInfFin.dvalue_convert_strict_equation in H.
    destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
    break_match_hyp; inv H1.
    exists x; auto.
  Qed.

  Lemma dvalue_convert_strict_i1_inv :
    forall x n,
      DVCInfFin.dvalue_convert_strict x = NoOom (DVCInfFin.DV2.DVALUE_I1 n) ->
      x = DVCInfFin.DV1.DVALUE_I1 n.
  Proof.
    intros x n H.
    rewrite DVCInfFin.dvalue_convert_strict_equation in H.
    destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
    subst.
    auto.
  Qed.

  Lemma dvalue_convert_strict_i8_inv :
    forall x n,
      DVCInfFin.dvalue_convert_strict x = NoOom (DVCInfFin.DV2.DVALUE_I8 n) ->
      x = DVCInfFin.DV1.DVALUE_I8 n.
  Proof.
    intros x n H.
    rewrite DVCInfFin.dvalue_convert_strict_equation in H.
    destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
    subst.
    auto.
  Qed.

  Lemma dvalue_convert_strict_i32_inv :
    forall x n,
      DVCInfFin.dvalue_convert_strict x = NoOom (DVCInfFin.DV2.DVALUE_I32 n) ->
      x = DVCInfFin.DV1.DVALUE_I32 n.
  Proof.
    intros x n H.
    rewrite DVCInfFin.dvalue_convert_strict_equation in H.
    destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
    subst.
    auto.
  Qed.

  Lemma dvalue_convert_strict_i64_inv :
    forall x n,
      DVCInfFin.dvalue_convert_strict x = NoOom (DVCInfFin.DV2.DVALUE_I64 n) ->
      x = DVCInfFin.DV1.DVALUE_I64 n.
  Proof.
    intros x n H.
    rewrite DVCInfFin.dvalue_convert_strict_equation in H.
    destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
    subst.
    auto.
  Qed.

  Lemma dvalue_convert_strict_double_inv :
    forall x v,
      DVCInfFin.dvalue_convert_strict x = NoOom (DVCInfFin.DV2.DVALUE_Double v) ->
      x = DVCInfFin.DV1.DVALUE_Double v.
  Proof.
    intros x n H.
    rewrite DVCInfFin.dvalue_convert_strict_equation in H.
    destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
    subst.
    auto.
  Qed.

  Lemma dvalue_convert_strict_float_inv :
    forall x v,
      DVCInfFin.dvalue_convert_strict x = NoOom (DVCInfFin.DV2.DVALUE_Float v) ->
      x = DVCInfFin.DV1.DVALUE_Float v.
  Proof.
    intros x n H.
    rewrite DVCInfFin.dvalue_convert_strict_equation in H.
    destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
    subst.
    auto.
  Qed.

  Lemma dvalue_convert_strict_poison_inv :
    forall x v,
      DVCInfFin.dvalue_convert_strict x = NoOom (DVCInfFin.DV2.DVALUE_Poison v) ->
      x = DVCInfFin.DV1.DVALUE_Poison v.
  Proof.
    intros x n H.
    rewrite DVCInfFin.dvalue_convert_strict_equation in H.
    destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
    subst.
    auto.
  Qed.

  Lemma dvalue_convert_strict_oom_inv :
    forall x v,
      DVCInfFin.dvalue_convert_strict x = NoOom (DVCInfFin.DV2.DVALUE_Oom v) ->
      x = DVCInfFin.DV1.DVALUE_Oom v.
  Proof.
    intros x n H.
    rewrite DVCInfFin.dvalue_convert_strict_equation in H.
    destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
    subst.
    auto.
  Qed.

  Lemma dvalue_convert_strict_none_inv :
    forall x,
      DVCInfFin.dvalue_convert_strict x = NoOom DVCInfFin.DV2.DVALUE_None ->
      x = DVCInfFin.DV1.DVALUE_None.
  Proof.
    intros x H.
    rewrite DVCInfFin.dvalue_convert_strict_equation in H.
    destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
    subst.
    auto.
  Qed.

  Lemma dvalue_convert_strict_struct_inv :
    forall x fields,
      DVCInfFin.dvalue_convert_strict x = NoOom (DVCInfFin.DV2.DVALUE_Struct fields) ->
      exists fields', x = DVCInfFin.DV1.DVALUE_Struct fields'.
  Proof.
    intros x fields H.
    rewrite DVCInfFin.dvalue_convert_strict_equation in H.
    destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
    break_match_hyp; inv H1.
    exists fields0. reflexivity.
  Qed.

  Lemma dvalue_convert_strict_packed_struct_inv :
    forall x fields,
      DVCInfFin.dvalue_convert_strict x = NoOom (DVCInfFin.DV2.DVALUE_Packed_struct fields) ->
      exists fields', x = DVCInfFin.DV1.DVALUE_Packed_struct fields'.
  Proof.
    intros x fields H.
    rewrite DVCInfFin.dvalue_convert_strict_equation in H.
    destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
    break_match_hyp; inv H1.
    exists fields0. reflexivity.
  Qed.

  Lemma dvalue_convert_strict_array_inv :
    forall x elts,
      DVCInfFin.dvalue_convert_strict x = NoOom (DVCInfFin.DV2.DVALUE_Array elts) ->
      exists elts', x = DVCInfFin.DV1.DVALUE_Array elts'.
  Proof.
    intros x elts H.
    rewrite DVCInfFin.dvalue_convert_strict_equation in H.
    destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
    break_match_hyp; inv H1.
    exists elts0. reflexivity.
  Qed.

  Lemma dvalue_convert_strict_vector_inv :
    forall x elts,
      DVCInfFin.dvalue_convert_strict x = NoOom (DVCInfFin.DV2.DVALUE_Vector elts) ->
      exists elts', x = DVCInfFin.DV1.DVALUE_Vector elts'.
  Proof.
    intros x elts H.
    rewrite DVCInfFin.dvalue_convert_strict_equation in H.
    destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
    break_match_hyp; inv H1.
    exists elts0. reflexivity.
  Qed.

  Lemma fin_inf_no_overlap :
    forall a1 sz1 a2 sz2 a1' a2',
      InfToFinAddrConvert.addr_convert a1' = NoOom a1 ->
      InfToFinAddrConvert.addr_convert a2' = NoOom a2 ->
      Memory64BitIntptr.MMEP.MemSpec.OVER_H.no_overlap a1 sz1 a2 sz2 = MemoryBigIntptr.MMEP.MemSpec.OVER_H.no_overlap a1' sz1 a2' sz2.
  Proof.
  Admitted.


  Lemma fin_inf_intptr_seq :
    forall start len ips,
      Memory64BitIntptr.MMEP.MemSpec.MemHelpers.intptr_seq start len = NoOom ips ->
      exists ips_big, MemoryBigIntptr.MMEP.MemSpec.MemHelpers.intptr_seq start len = NoOom ips_big /\
                   Forall2 (fun a b => LLVMParams64BitIntptr.IP.to_Z a = LLVMParamsBigIntptr.IP.to_Z b) ips ips_big.
  Proof.
    intros start len ips SEQ.
    pose proof Memory64BitIntptr.MMEP.MemSpec.MemHelpers.intptr_seq_len _ _ _ SEQ as LEN.
    generalize dependent start.
    generalize dependent len.
    induction ips; intros len LEN start SEQ.
    - cbn in *; subst.
      exists [].
      split.
      + cbn; auto.
      + constructor.
    - cbn in *; inv LEN.
      pose proof SEQ.
      rewrite Memory64BitIntptr.MMEP.MemSpec.MemHelpers.intptr_seq_succ in H0.
      cbn in H0.
      break_match_hyp; inv H0.
      break_match_hyp; inv H2.

      pose proof Heqo.
      apply fin_inf_from_Z in Heqo as [ip_i IP_I].
      specialize (IHips (Datatypes.length ips) eq_refl (Z.succ start) Heqo0).
      destruct IHips as [ips_big [SEQ' ALL]].
      exists (ip_i :: ips_big).
      split.
      + rewrite MemoryBigIntptr.MMEP.MemSpec.MemHelpers.intptr_seq_succ.
        cbn.
        rewrite SEQ'.
        cbn in IP_I.
        inv IP_I.
        auto.
      + constructor; eauto.
        eapply fin_inf_from_Z_to_Z; eauto.
  Qed.

  Lemma fin_inf_get_consecutive_ptrs_success :
    forall a a' n ms ms_x xs ms_y ys,
      (* TODO: ADDR probably not necessary, can conclude this from ADDRS...
       *)
      InfToFinAddrConvert.addr_convert a' = NoOom a ->
      Forall2 (fun x y => InfToFinAddrConvert.addr_convert y = NoOom x) xs ys ->
      (@Memory64BitIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs
         (MemPropT Memory64BitIntptr.MMEP.MMSP.MemState)
         (@MemPropT_Monad Memory64BitIntptr.MMEP.MMSP.MemState)
         (@MemPropT_RAISE_OOM Memory64BitIntptr.MMEP.MMSP.MemState)
         (@MemPropT_RAISE_ERROR Memory64BitIntptr.MMEP.MMSP.MemState) a n ms (success_unERR_UB_OOM (ms_x, xs))) ->
      (@MemoryBigIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs
         (MemPropT MemoryBigIntptr.MMEP.MMSP.MemState)
         (@MemPropT_Monad MemoryBigIntptr.MMEP.MMSP.MemState)
         (@MemPropT_RAISE_OOM MemoryBigIntptr.MMEP.MMSP.MemState)
         (@MemPropT_RAISE_ERROR MemoryBigIntptr.MMEP.MMSP.MemState) a' n ms_y (success_unERR_UB_OOM (ms_y, ys))).
  Proof.
    intros a a' n ms ms_x xs ms_y ys A'A ADDRS CONSEC.
    cbn in *.
    destruct CONSEC as [sab [a0 [SEQ_OOM CONSEC]]].
    destruct (Memory64BitIntptr.MMEP.MemSpec.MemHelpers.intptr_seq 0 n) eqn:SEQ; cbn in *; try contradiction.
    destruct SEQ_OOM; subst.

    destruct CONSEC as [sab [addrs CONSEC]].

    pose proof (fin_inf_intptr_seq _ _ _ SEQ).
    destruct H as [lb [SEQ_BIG ALL]].
    exists ms_y. exists lb.
    split.
    { rewrite SEQ_BIG.
      cbn; auto.
    }

    destruct CONSEC as [GEN_ADDRS SEQ_ADDRS].
    destruct (map_monad
                (fun ix : LLVMParams64BitIntptr.IP.intptr =>
                   inr
                     (LLVMParams64BitIntptr.ITOP.int_to_ptr
                        (LLVMParams64BitIntptr.PTOI.ptr_to_int a +
                           Z.of_N (LLVMParams64BitIntptr.SIZEOF.sizeof_dtyp (DTYPE_I 8)) *
                             LLVMParams64BitIntptr.IP.to_Z ix)
                        (LLVMParams64BitIntptr.PROV.address_provenance a))) l) eqn:HMAPM; cbn in *; try contradiction.

    destruct GEN_ADDRS; subst.

    destruct (@map_monad err (EitherMonad.Monad_either string) LLVMParamsBigIntptr.IP.intptr
                (OOM LLVMParamsBigIntptr.ADDR.addr)
                (fun ix : LLVMParamsBigIntptr.IP.intptr =>
                   @inr string (OOM LLVMParamsBigIntptr.ADDR.addr)
                     (@NoOom (Z * Prov)
                        ((LLVMParamsBigIntptr.PTOI.ptr_to_int a' +
                            Z.of_N (LLVMParamsBigIntptr.SIZEOF.sizeof_dtyp (DTYPE_I 8)) *
                              LLVMParamsBigIntptr.IP.to_Z ix)%Z, LLVMParamsBigIntptr.PROV.address_provenance a')))
                lb) eqn:HMAPM'.
    { (* Should be a contradiction *)
      apply map_monad_err_fail in HMAPM'.
      destruct HMAPM' as [a'' [IN CONTRA]].
      inv CONTRA.
    }

    exists ms_y. exists l1.
    split.
    {
      red.
      (* I have no clue why this rewrite won't work *)
      (* rewrite HMAPM'. *)
      break_match_goal.
      { apply map_monad_err_fail in Heqs.
        destruct Heqs as [a'' [IN CONTRA]].
        inv CONTRA.
      }
      setoid_rewrite HMAPM' in Heqs.
      inv Heqs.

      cbn.
      split; reflexivity.
    }

    red.
    break_match_goal.
    2: {
      (* TODO: There's probably a nice lemma in here *)
      cbn.
      apply map_monad_OOM_fail in Heqo.
      destruct Heqo as [x [INx OOMx]].
      unfold id in OOMx.
      inv OOMx.

      apply map_monad_err_forall2 in HMAPM'.
      apply Util.Forall2_forall in HMAPM' as [LEN HMAPM'].
      apply In_Nth in INx. destruct INx as [i NTHl1].

      epose proof (Nth_exists lb i) as NTHlb.
      forward NTHlb.
      { apply Nth_ix_lt_length in NTHl1.
        lia.
      }
      destruct NTHlb as (?&NTHlb).
      specialize (HMAPM' _ _ _ NTHlb NTHl1).
      inv HMAPM'.
    }

    cbn.

    split; auto.

    { (* Might follow from ADDRS? *)
      red in SEQ_ADDRS.
      break_match_hyp; cbn in *; try contradiction.
      inv SEQ_ADDRS.
      rename l3 into xs.
      rename l0 into oxs.
      rename l into ixs.
      rename lb into ixs_big.
      rename l1 into oys.
      rename l2 into ys'.

      (* Each y in ys should match up with a y in ys'... I.e.,

                                     forall i y y', Util.Nth ys i y -> Util.Nth ys' i y' -> y = y'

                                     Why?

                                     HMAPM' / Heqo should yield: y' = a' + i
                                     ADDRS should suggest that y = xs[i]
                                     HMAPM / Heqo0 yields xs[i] = a + i

       *)

      assert (forall i y y', Util.Nth ys i y -> Util.Nth ys' i y' -> y = y') as NTHysys'.
      {
        intros i y y' H H0.

        (* Figure out what y' is *)
        pose proof (map_monad_OOM_Nth _ _ _ y' i Heqo H0) as [y'' [Y NTHoys]].
        unfold id in Y. cbn in Y. inv Y. clear H1.
        pose proof (map_monad_err_Nth _ _ _ _ i HMAPM' NTHoys) as [y'' [Y NTHixs_big]].
        inv Y.

        (* Figure out what y is *)
        pose proof (Util.Forall2_Nth_right H ADDRS) as [x [NTHxs CONVxy]].
        pose proof (map_monad_OOM_Nth _ _ _ x i Heqo0 NTHxs) as [x'' [X NTHoxs]].
        unfold id in X. cbn in X. inv X. clear H1.
        pose proof (map_monad_err_Nth _ _ _ _ i HMAPM NTHoxs) as [x'' [X NTHixs]].
        inv X.

        eapply InfToFinAddrConvert.addr_convert_injective; eauto.
        unfold InfToFinAddrConvert.addr_convert.

        assert (LLVMParams64BitIntptr.IP.to_Z x'' = LLVMParamsBigIntptr.IP.to_Z y'') as X''Y''.
        {
          eapply fin_inf_from_Z_to_Z.
          - apply (MemoryBigIntptr.MMEP.MemSpec.MemHelpers.intptr_seq_nth 0 n _ i y'' SEQ_BIG NTHixs_big).
          - apply (Memory64BitIntptr.MMEP.MemSpec.MemHelpers.intptr_seq_nth 0 n _ i x'' SEQ NTHixs).
        }
        rewrite <- X''Y''.

        rewrite LLVMParamsBigIntptr.SIZEOF.sizeof_dtyp_i8.
        rewrite LLVMParams64BitIntptr.SIZEOF.sizeof_dtyp_i8 in H2.

        pose proof ADDRS.
        inversion H1; subst.
        { apply Util.not_Nth_nil in NTHxs.
          contradiction.
        }

        rename l into xs.
        rename l' into ys.

        (* x0 and y0 should correspond to a and a' *)
        assert (x0 = a).
        {
          eapply map_monad_OOM_Nth with (n:=0%nat) in Heqo0; cbn; eauto.
          destruct Heqo0 as (x0'&X0&NTHx0).
          unfold id in X0. subst.
          eapply map_monad_err_Nth with (n:=0%nat) in HMAPM; cbn; eauto.
          destruct HMAPM as (x0''&X0&NTHx0').
          cbn in *.
          inv X0.

          destruct ixs; inv NTHx0'.
          destruct n; inv SEQ.
          cbn in *.
          rewrite IP64Bit.from_Z_0 in H7.
          break_match_hyp; inv H7.
          rewrite IP64Bit.to_Z_0 in H6.
          replace (LLVMParams64BitIntptr.PTOI.ptr_to_int a +
                     Z.of_N (LLVMParams64BitIntptr.SIZEOF.sizeof_dtyp (DTYPE_I 8)) * 0)%Z with (LLVMParams64BitIntptr.PTOI.ptr_to_int a) in H6 by lia.

          pose proof LLVMParams64BitIntptr.ITOP.int_to_ptr_ptr_to_int a (LLVMParams64BitIntptr.PROV.address_provenance a) eq_refl.
          rewrite H6 in H5.
          inv H5.
          reflexivity.
        }
        subst.

        assert (y0 = a').
        { eapply InfToFinAddrConvert.addr_convert_injective.
          eapply H3.
          eauto.
        }
        subst.

        rewrite <- H2.
        destruct a' as (ptr', pr').
        erewrite fin_inf_ptoi; eauto.
        erewrite FinLP.ITOP.int_to_ptr_provenance; eauto.
      }

      eapply Nth_eq; eauto.
      (* Length:

                                     ys = xs = oxs = ixs = n
                                     ys' = oys = ixs_big = n
       *)

      apply Util.Forall2_length in ADDRS, ALL.
      apply map_monad_err_length in HMAPM, HMAPM'.
      apply map_monad_oom_length in Heqo, Heqo0.
      congruence.
    }
  Qed.

  Lemma inf_fin_addr_convert_provenance :
    forall a_inf a_fin,
      InfToFinAddrConvert.addr_convert a_inf = NoOom a_fin ->
      LLVMParamsBigIntptr.PROV.address_provenance a_inf = LLVMParams64BitIntptr.PROV.address_provenance a_fin.
  Proof.
    intros a_inf a_fin ADDR_CONV.
    destruct a_inf, a_fin.
    cbn in *.
    apply ITOP.int_to_ptr_provenance in ADDR_CONV.
    cbn in *.
    auto.
  Qed.

  Lemma fin_inf_get_consecutive_ptrs_success_exists' :
    forall a_fin a_inf n ms_fin ms_fin' addrs_fin ms_inf,
      (* TODO: ADDR probably not necessary, can conclude this from ADDRS...
       *)
      InfToFinAddrConvert.addr_convert a_inf = NoOom a_fin ->
      (@Memory64BitIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs
         (MemPropT Memory64BitIntptr.MMEP.MMSP.MemState)
         (@MemPropT_Monad Memory64BitIntptr.MMEP.MMSP.MemState)
         (@MemPropT_RAISE_OOM Memory64BitIntptr.MMEP.MMSP.MemState)
         (@MemPropT_RAISE_ERROR Memory64BitIntptr.MMEP.MMSP.MemState) a_fin n ms_fin (success_unERR_UB_OOM (ms_fin', addrs_fin))) ->
      exists addrs_inf,
        (@MemoryBigIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs
           (MemPropT MemoryBigIntptr.MMEP.MMSP.MemState)
           (@MemPropT_Monad MemoryBigIntptr.MMEP.MMSP.MemState)
           (@MemPropT_RAISE_OOM MemoryBigIntptr.MMEP.MMSP.MemState)
           (@MemPropT_RAISE_ERROR MemoryBigIntptr.MMEP.MMSP.MemState) a_inf n ms_inf (success_unERR_UB_OOM (ms_inf, addrs_inf))) /\
          Forall2 (fun x y => InfToFinAddrConvert.addr_convert y = NoOom x) addrs_fin addrs_inf.
  Proof.
    intros a_fin a_inf n ms_fin ms_fin' addrs_fin ms_inf ADDR_CONV GCP.
    pose proof fin_inf_get_consecutive_ptrs_success a_fin a_inf n ms_fin ms_fin' addrs_fin ms_inf.
    pose proof MemoryBigIntptrInfiniteSpec.MSIH.big_intptr_seq_succeeds 0 n as (ips & SEQ_INF).
    pose proof
      map_monad_err_succeeds
      (fun ix : LLVMParamsBigIntptr.IP.intptr =>
         @inr string (OOM LLVMParamsBigIntptr.ADDR.addr)
           (@NoOom (Z * Prov)
              ((LLVMParamsBigIntptr.PTOI.ptr_to_int a_inf +
                  Z.of_N (LLVMParamsBigIntptr.SIZEOF.sizeof_dtyp (DTYPE_I 8)) *
                    LLVMParamsBigIntptr.IP.to_Z ix)%Z, LLVMParamsBigIntptr.PROV.address_provenance a_inf)))
      ips as ADDRS_INF.
    forward ADDRS_INF.
    { intros a IN.
      eexists; reflexivity.
    }

    destruct ADDRS_INF as [oaddrs_inf ADDRS_INF].

    pose proof
      map_monad_oom_succeeds id oaddrs_inf as SEQ.
    forward SEQ.
    {
      intros a IN.
      epose proof map_monad_err_In _ _ _ _ ADDRS_INF IN as (y&A&INy).
      inv A.
      eexists.
      unfold id.
      reflexivity.
    }
    destruct SEQ as (RES&MAP_INF).

    cbn.
    eexists.
    split.
    { eexists.
      eexists.
      split.
      - red.
        rewrite SEQ_INF.
        cbn.
        split; auto.
      - eexists. eexists.
        split.
        + red.
          (* TODO: Why can't I rewrite with ADDRS_INF? *)
          break_match_goal;
            setoid_rewrite ADDRS_INF in Heqs;
            inv Heqs.
          cbn.
          split; auto.
        + red.
          unfold Monads.sequence.
          rewrite MAP_INF.
          cbn.
          split; reflexivity.
    }

    apply Util.Forall2_forall.
    split.
    - apply map_monad_oom_length in MAP_INF.
      apply map_monad_err_length in ADDRS_INF.

      (* Need something about get_consecutive_ptrs_length...

                             There is one: FinLLVM.MEM.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs_length.

                             Need to refresh memory on Within, though.
       *)

      assert (n = Datatypes.length addrs_fin) as ADDRS_FIN_LEN.
      {
        assert (exists (pre : Memory64BitIntptr.MMEP.MMSP.MemState) (post : Memory64BitIntptr.MMEP.MMSP.MemState),
                   Within.within (FinLLVM.MEM.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs a_fin n) pre
                     (ret addrs_fin) post).
        {
          exists FinMemMMSP.initial_memory_state. exists FinMemMMSP.initial_memory_state.
          cbn.
          exists FinMemMMSP.initial_memory_state.

          red in GCP.
          destruct (Memory64BitIntptr.MMEP.MemSpec.MemHelpers.intptr_seq 0 n) eqn:SEQ_FIN; cbn in GCP.
          2: { destruct GCP as [sab [a [[] _]]]. }

          destruct GCP as [sab [a [[MS A] GCP]]]; subst.
          destruct GCP as [sab [a [GCP SEQ]]]; subst.
          destruct (map_monad
                      (fun ix : LLVMParams64BitIntptr.IP.intptr =>
                         inr
                           (LLVMParams64BitIntptr.ITOP.int_to_ptr
                              (LLVMParams64BitIntptr.PTOI.ptr_to_int a_fin +
                                 Z.of_N (LLVMParams64BitIntptr.SIZEOF.sizeof_dtyp (DTYPE_I 8)) *
                                   LLVMParams64BitIntptr.IP.to_Z ix)
                              (LLVMParams64BitIntptr.PROV.address_provenance a_fin))) l) eqn:HMAPM; cbn in GCP; try contradiction.
          destruct GCP; subst.
          red in SEQ.
          break_match_hyp; inv SEQ.

          eexists; split; cbn; eauto.
          exists FinMemMMSP.initial_memory_state.
          eexists; split; cbn; eauto.
          rewrite HMAPM.
          cbn; eauto.
          rewrite Heqo. cbn. auto.
        }

        pose proof FinLLVM.MEM.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs_length _ _ _ H0; eauto.
      }

      apply MemoryBigIntptr.MMEP.MemSpec.MemHelpers.intptr_seq_len in SEQ_INF.
      congruence.
    - intros i a b NTHaddrs NTHres.
      pose proof (map_monad_OOM_Nth _ _ _ _ _ MAP_INF NTHres) as (y&Y&NTHoaddrs).
      unfold id in Y; subst.

      pose proof (map_monad_err_Nth _ _ _ _ _ ADDRS_INF NTHoaddrs) as (y&Y&NTHips).
      cbn in Y. inv Y.

      rename a into ptr_fin.

      (* Need to break apart GCP to find out about ptr_fin *)
      pose proof Memory64BitIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs_nth_eq1 a_fin n addrs_fin.
      forward H0.
      {
        red. red.
        intros ms x.
        split.
        - intros GCP'.
          cbn.
          destruct_err_ub_oom x.
          + (* Contradiction *)
            cbn in GCP'.
            clear H0.
            cbn in GCP.
            move GCP after GCP'.
            destruct GCP as [ms' [a [SEQ GCP]]].
            red in SEQ.
            break_match_hyp; inv SEQ.

            destruct GCP'.
            cbn in H0; auto.

            destruct H0 as [sab [a [[MS LA] GCP']]].
            subst.

            destruct GCP as [ms' [a [GCP SEQ_FIN]]].
            red in GCP.
            break_match_hyp; inv GCP.
            rename Heqs into GCP.

            red in SEQ_FIN.
            break_match_hyp; inv SEQ_FIN.

            destruct GCP' as [GCP' | GCP'];
              cbn in *; auto.

            destruct GCP' as [sab [a [[MS LA] SEQ]]].
            subst.

            rewrite Heqo0 in SEQ.
            cbn in SEQ.
            auto.
          + (* Contradiction *)
            cbn in GCP'.
            clear H0.
            cbn in GCP.
            move GCP after GCP'.
            destruct GCP as [ms' [a [SEQ GCP]]].
            red in SEQ.
            break_match_hyp; inv SEQ.

            destruct GCP'.
            cbn in H0; auto.

            destruct H0 as [sab [a [[MS LA] GCP']]].
            subst.

            destruct GCP as [ms' [a [GCP SEQ_FIN]]].
            red in GCP.
            break_match_hyp; inv GCP.
            rename Heqs into GCP.

            red in SEQ_FIN.
            break_match_hyp; inv SEQ_FIN.

            destruct GCP' as [GCP' | GCP'];
              cbn in *; auto.

            destruct GCP' as [sab [a [[MS LA] SEQ]]].
            subst.

            rewrite Heqo0 in SEQ.
            cbn in SEQ.
            auto.
          + (* Contradiction *)
            cbn in GCP'.
            clear H0.
            cbn in GCP.
            move GCP after GCP'.
            destruct GCP as [ms' [a [SEQ GCP]]].
            red in SEQ.
            break_match_hyp; inv SEQ.

            destruct GCP'.
            cbn in H0; auto.

            destruct H0 as [sab [a [[MS LA] GCP']]].
            subst.

            destruct GCP as [ms' [a [GCP SEQ_FIN]]].
            red in GCP.
            break_match_hyp; inv GCP.
            rename Heqs into GCP.

            red in SEQ_FIN.
            break_match_hyp; inv SEQ_FIN.

            destruct GCP' as [GCP' | GCP'];
              cbn in *; auto.

            destruct GCP' as [sab [a [[MS LA] SEQ]]].
            subst.

            rewrite Heqo0 in SEQ.
            cbn in SEQ.
            auto.
          + destruct x0.
            inv Hx.
            (* Should be able to conclude this with a mix of GCP' and GCP *)
            cbn in *.
            destruct GCP' as [ms' [a [SEQ_FIN GCP']]].
            red in SEQ_FIN.
            break_match_hyp; inv SEQ_FIN.
            destruct GCP' as [sab [a [GCP' SEQ_FIN]]].

            red in SEQ_FIN.
            break_match_hyp; inv SEQ_FIN.

            red in GCP'.
            break_match_hyp; inv GCP'.
            split; auto.

            destruct GCP as [ms' [a [[MS L] GCP]]].
            subst.
            destruct GCP as [ms' [a [GCP SEQ]]].
            red in GCP.
            break_match_hyp; inv GCP.
            red in SEQ.
            break_match_hyp; inv SEQ.

            clear H0 H.
            inv Heqs.
            rewrite Heqo1 in Heqo0.
            inv Heqo0.
            reflexivity.
        - intros RET.
          cbn in RET.
          destruct_err_ub_oom x; try inv RET.
          destruct x0.
          destruct RET; subst.

          red in GCP.
          destruct (Memory64BitIntptr.MMEP.MemSpec.MemHelpers.intptr_seq 0 n) eqn:SEQ_FIN; cbn in GCP.
          2: { destruct GCP as [sab [a [[] _]]]. }
          destruct GCP as [sab [a [[MS A] GCP]]]; subst.
          destruct GCP as [sab [a [GCP SEQ]]]; subst.
          destruct (map_monad
                      (fun ix : LLVMParams64BitIntptr.IP.intptr =>
                         inr
                           (LLVMParams64BitIntptr.ITOP.int_to_ptr
                              (LLVMParams64BitIntptr.PTOI.ptr_to_int a_fin +
                                 Z.of_N (LLVMParams64BitIntptr.SIZEOF.sizeof_dtyp (DTYPE_I 8)) *
                                   LLVMParams64BitIntptr.IP.to_Z ix)
                              (LLVMParams64BitIntptr.PROV.address_provenance a_fin))) l) eqn:HMAPM; cbn in GCP; try contradiction.
          destruct GCP; subst.
          red in SEQ.
          break_match_hyp; inv SEQ.

          cbn.
          exists ms. exists l.
          split.
          rewrite SEQ_FIN; cbn; auto.

          exists ms. exists l0.
          rewrite HMAPM. cbn.
          split; auto.
          rewrite Heqo; cbn; auto.
      }

      specialize (H0 _ _ NTHaddrs).
      destruct H0 as [ip [IP GEP]].
      pose proof GEP as GEP'.
      apply FinLLVM.MEM.MP.GEP.handle_gep_addr_ix in GEP.

      assert (LLVMParamsBigIntptr.IP.to_Z y = Z.of_nat i) as IPI.
      { pose proof MemoryBigIntptr.MMEP.MemSpec.MemHelpers.intptr_seq_nth _ _ _ _ _ SEQ_INF NTHips.
        replace (0 + (Z.of_nat i))%Z with (Z.of_nat i) in H0 by lia.
        eapply FiniteIntptr.BigIP.from_Z_to_Z.
        apply H0.
      }
      rewrite IPI.

      symmetry in IP.
      eapply FinLP.IP.from_Z_to_Z in IP.
      rewrite IP in GEP.

      replace (LLVMParamsBigIntptr.PTOI.ptr_to_int a_inf +
                 Z.of_N (LLVMParamsBigIntptr.SIZEOF.sizeof_dtyp (DTYPE_I 8)) * Z.of_nat i)%Z with (PTOI.ptr_to_int ptr_fin).
      2: {
        rewrite GEP.
        erewrite fin_inf_ptoi; eauto.
      }

      pose proof GEP' as GEP''.
      apply Memory64BitIntptr.GEP.handle_gep_addr_preserves_provenance in GEP'.

      erewrite inf_fin_addr_convert_provenance; eauto.
      rewrite GEP'.

      cbn.
      apply ITOP.int_to_ptr_ptr_to_int.
      reflexivity.
  Qed.

  (* Form that better matches MemPropT_fin_inf_bind *)
  Lemma fin_inf_get_consecutive_ptrs_success_exists :
    forall a_fin a_inf n ms_fin ms_fin' addrs_fin ms_inf,
      (* TODO: ADDR probably not necessary, can conclude this from ADDRS...
       *)
      InfToFinAddrConvert.addr_convert a_inf = NoOom a_fin ->
      MemState_refine_prop ms_inf ms_fin ->
      (@Memory64BitIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs
         (MemPropT Memory64BitIntptr.MMEP.MMSP.MemState)
         (@MemPropT_Monad Memory64BitIntptr.MMEP.MMSP.MemState)
         (@MemPropT_RAISE_OOM Memory64BitIntptr.MMEP.MMSP.MemState)
         (@MemPropT_RAISE_ERROR Memory64BitIntptr.MMEP.MMSP.MemState) a_fin n ms_fin (success_unERR_UB_OOM (ms_fin', addrs_fin))) ->
      exists addrs_inf ms_inf',
        (@MemoryBigIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs
           (MemPropT MemoryBigIntptr.MMEP.MMSP.MemState)
           (@MemPropT_Monad MemoryBigIntptr.MMEP.MMSP.MemState)
           (@MemPropT_RAISE_OOM MemoryBigIntptr.MMEP.MMSP.MemState)
           (@MemPropT_RAISE_ERROR MemoryBigIntptr.MMEP.MMSP.MemState) a_inf n ms_inf (success_unERR_UB_OOM (ms_inf', addrs_inf))) /\
          Forall2 (fun x y => InfToFinAddrConvert.addr_convert y = NoOom x) addrs_fin addrs_inf /\
          MemState_refine_prop ms_inf' ms_fin'.
  Proof.
    intros a_fin a_inf n ms_fin ms_fin' addrs_fin ms_inf ADDR_CONV MSR GCP.

    pose proof fin_inf_get_consecutive_ptrs_success_exists' a_fin a_inf n ms_fin ms_fin' addrs_fin ms_inf ADDR_CONV GCP.
    destruct H as (addrs_inf & GCP' & ADDRS).
    exists addrs_inf. exists ms_inf.
    split; auto.
    split; auto.
    apply FinMem.MMEP.get_consecutive_ptrs_MemPropT_MemState_eq in GCP; subst; auto.
  Qed.

  (* TODO: Maybe change MemState_refine to be propositional in terms of find *)

  Lemma IntMap_find_NoOom_assoc_list :
    forall {X Y} (l : list (IntMaps.IM.key * X)) (f : (IntMaps.IM.key * X) -> OOM (IntMaps.IM.key * Y)) m_elts (n : Z) (y : Y),
      SetoidList.NoDupA (IntMaps.IM.eq_key (elt:=X)) l ->
      map_monad f l = NoOom m_elts ->
      (forall '(ix, x) '(ix', y), f (ix, x) = NoOom (ix', y) -> ix = ix') ->
      IntMaps.IM.find (elt:=Y) n (IntMaps.IP.of_list m_elts) = Some y ->
      exists x, SetoidList.findA (IntMaps.IP.F.eqb n) l = Some x /\ NoOom (n, y) = f (n, x).
  Proof.
    induction l; intros f m_elts n y NODUP HMAPM F FIND.
    - cbn in *.
      inv HMAPM.
      cbn in *.
      inv FIND.
    - cbn in *.
      break_match_hyp; [|inv HMAPM].
      break_match_hyp; [|inv HMAPM].
      inv HMAPM.
      destruct a as [a_k a_v].
      destruct p as [p_k p_v].
      pose proof (F (a_k, a_v) (p_k, p_v) Heqo); subst.
      Opaque IntMaps.IM.find.
      Opaque IntMaps.IM.add.
      cbn in *.
      break_match_goal.
      + (* New element *)
        exists a_v.
        split; auto.
        unfold IntMaps.IP.F.eqb in Heqb.
        break_match_hyp; subst; try discriminate.
        unfold IntMaps.IP.uncurry in FIND.
        rewrite IntMaps.IP.F.add_eq_o in FIND; cbn; auto.
        cbn in FIND.
        inv FIND.
        auto.
      + (* Old element *)
        inversion NODUP; subst.
        rename H1 into NIN.
        rename H2 into NODUP'.

        unfold IntMaps.IP.F.eqb in Heqb.
        break_match_hyp; subst; try discriminate.
        unfold IntMaps.IP.uncurry in FIND.
        rewrite IntMaps.IP.F.add_neq_o in FIND; cbn; auto.

        eauto.
  Qed.

  (* TODO: a little unsure of this one, but it seems plausible. *)
  Lemma fin_to_inf_uvalue_refine_strict' :
    forall d_inf d_fin,
      DVC1.uvalue_refine_strict d_inf d_fin ->
      d_inf = fin_to_inf_uvalue d_fin.
  Proof.
    intros d_inf d_fin H.
    rewrite DVC1.uvalue_refine_strict_equation in H.
    unfold fin_to_inf_uvalue.
    break_match; cbn in *.
    destruct p.
    clear Heqs.

    induction d_inf;
      try solve
        [ rewrite DVC1.uvalue_convert_strict_equation in H;
          cbn in *; inv H;
          rewrite DVC2.uvalue_convert_strict_equation in e;
          cbn in *; inv e;
          auto
        ].
    - rewrite DVC1.uvalue_convert_strict_equation in H.
      cbn in *.
      break_match_hyp; inv H.
      rewrite DVC2.uvalue_convert_strict_equation in e.
      cbn in *.
      break_match_hyp; inv e.
      rewrite DVC1.uvalue_convert_strict_equation in e0.
      cbn in *.
      break_match_hyp; inv e0.

      pose proof InfToFinAddrConvert.addr_convert_injective a a1 a0 Heqo Heqo1.
      subst.
      auto.
    - rewrite DVC1.uvalue_convert_strict_equation in H.
      cbn in *; break_match_hyp; inv H.
      rewrite DVC2.uvalue_convert_strict_equation in e.
      cbn in *; inv e.
      rewrite DVC1.uvalue_convert_strict_equation in e0.
      cbn in *; break_match_hyp; inv e0.
      admit. (* Some painful IP / BigIP reasoning *)
    - rewrite DVC1.uvalue_convert_strict_equation in H.
      cbn in *; break_match_hyp; inv H.
      rewrite DVC2.uvalue_convert_strict_equation in e.
      cbn in *; break_match_hyp; inv e.
      rewrite DVC1.uvalue_convert_strict_equation in e0.
      cbn in *; break_match_hyp; inv e0.

      induction fields.
      + cbn in *. inv Heqo.
        cbn in *. inv Heqo0.
        reflexivity.
      + rewrite map_monad_InT_unfold in Heqo.
        cbn in *.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H1.

        rewrite map_monad_InT_unfold in Heqo0.
        cbn in *.
        break_match_hyp; inv Heqo0.
        break_match_hyp; inv H1.

        rewrite map_monad_InT_unfold in Heqo1.
        cbn in *.
        break_match_hyp; inv Heqo1.
        break_match_hyp; inv H1.
        admit.
    - admit.
    - admit.
    - admit.
  Admitted.

  Lemma IntMap_find_NoOom_elements :
    forall {X Y} (m : IntMaps.IM.t X) (f : (IntMaps.IM.key * X) -> OOM (IntMaps.IM.key * Y)) m_elts (n : Z) (y : Y),
      map_monad f (IntMaps.IM.elements (elt:=X) m) = NoOom m_elts ->
      (forall '(ix, x) '(ix', y), f (ix, x) = NoOom (ix', y) -> ix = ix') ->
      IntMaps.IM.find (elt:=Y) n (IntMaps.IP.of_list m_elts) = Some y ->
      exists x, IntMaps.IM.find (elt:=X) n m = Some x /\ NoOom (n, y) = f (n, x).
  Proof.
    intros X Y m f m_elts n y HMAPM F FIND.
    pose proof IntMaps.IP.F.elements_o.
    setoid_rewrite H.
    eapply IntMap_find_NoOom_assoc_list.
    2: {
      exact HMAPM.
    }
    all: auto.
    apply IntMaps.IM.elements_3w.
  Qed.

  (* TODO: Move this somewhere it can apply to fin / inf *)
  Lemma memory_stack_memory_mem_state_memory :
    forall m,
      InfMem.MMEP.MMSP.memory_stack_memory (InfMem.MMEP.MMSP.MemState_get_memory m) = MemoryBigIntptrInfiniteSpec.MMSP.mem_state_memory m.
  Proof.
    intros m.
    destruct m.
    cbn.
    destruct ms_memory_stack.
    cbn.
    auto.
  Qed.

  (* TODO: Move this somewhere it can apply to fin / inf *)
  Lemma memory_stack_memory_mem_state_memory_fin :
    forall m,
      FinMem.MMEP.MMSP.memory_stack_memory (FinMem.MMEP.MMSP.MemState_get_memory m) = FinMemMMSP.mem_state_memory m.
  Proof.
    intros m.
    destruct m.
    cbn.
    destruct ms_memory_stack.
    cbn.
    auto.
  Qed.

  Lemma read_byte_raw_lifted :
    forall mem byte_lifted addr aid,
      InfMem.MMEP.MMSP.read_byte_raw (lift_memory mem) addr = Some (byte_lifted, aid) ->
      exists byte_fin : Memory64BitIntptr.MP.BYTE_IMPL.SByte,
        Memory64BitIntptr.MMEP.MMSP.read_byte_raw mem
          addr = Some (byte_fin, aid) /\
          sbyte_refine byte_lifted byte_fin.
  Proof.
    intros mem byte_lifted addr aid READ.
    Transparent Memory64BitIntptr.MMEP.MMSP.read_byte_raw.
    Transparent MemoryBigIntptr.MMEP.MMSP.read_byte_raw.
    unfold Memory64BitIntptr.MMEP.MMSP.read_byte_raw.
    unfold MemoryBigIntptr.MMEP.MMSP.read_byte_raw in READ.

    unfold lift_memory in READ.
    rewrite IntMaps.IP.F.map_o in READ.
    apply Util.option_map_some_inv in READ.
    destruct READ as [[byte_fin aid'] [FIND BYTE]].
    exists byte_fin.
    cbn in BYTE.
    inv BYTE.
    split; auto.
    apply sbyte_refine_lifted.

    Opaque Memory64BitIntptr.MMEP.MMSP.read_byte_raw.
    Opaque MemoryBigIntptr.MMEP.MMSP.read_byte_raw.
  Qed.

  Lemma read_byte_raw_lifted_fin_inf :
    forall mem byte_fin addr aid,
      Memory64BitIntptr.MMEP.MMSP.read_byte_raw mem addr = Some (byte_fin, aid) ->
      InfMem.MMEP.MMSP.read_byte_raw (lift_memory mem) addr = Some (lift_SByte byte_fin, aid).
  Proof.
    intros mem byte_lifted addr aid READ.
    Transparent Memory64BitIntptr.MMEP.MMSP.read_byte_raw.
    Transparent MemoryBigIntptr.MMEP.MMSP.read_byte_raw.
    unfold Memory64BitIntptr.MMEP.MMSP.read_byte_raw in READ.
    unfold MemoryBigIntptr.MMEP.MMSP.read_byte_raw.

    unfold lift_memory.
    rewrite IntMaps.IP.F.map_o.
    rewrite READ.
    cbn.
    reflexivity.

    Opaque Memory64BitIntptr.MMEP.MMSP.read_byte_raw.
    Opaque MemoryBigIntptr.MMEP.MMSP.read_byte_raw.
  Qed.

  (* TODO: Some tricky IntMap reasoning *)
  Lemma fin_inf_read_byte_raw :
    forall {m_inf m_fin ptr byte_fin aid},
      MemState_refine_prop m_inf m_fin ->
      Memory64BitIntptr.MMEP.MMSP.read_byte_raw
        (Memory64BitIntptr.MMEP.MMSP.mem_state_memory m_fin)
        ptr = Some (byte_fin, aid) ->
      MemoryBigIntptr.MMEP.MMSP.read_byte_raw
        (MemoryBigIntptrInfiniteSpec.MMSP.mem_state_memory m_inf)
        ptr = Some (lift_SByte byte_fin, aid).
  Proof.
    intros m_inf m_fin addr byte_fin aid MSR READ_RAW.

    destruct MSR.
    destruct H0.
    clear H1 H.
    destruct H0 as [ALLOWED RBP].
    unfold InfMem.MMEP.MemSpec.read_byte_prop_all_preserved in RBP.
    remember (addr, MemoryBigIntptrInfiniteSpec.LP.PROV.allocation_id_to_prov aid) as ptr_inf.
    specialize (RBP ptr_inf (lift_SByte byte_fin)).
    specialize (ALLOWED ptr_inf).

    assert (InfMem.MMEP.MemSpec.read_byte_prop (lift_MemState m_fin) ptr_inf (lift_SByte byte_fin)) as RBP_INF.
    {
      repeat red.
      exists (InfMem.MMEP.MMSP.MemState_get_memory (lift_MemState m_fin)).
      exists (InfMem.MMEP.MMSP.MemState_get_memory (lift_MemState m_fin)).

      split.
      cbn; auto.

      subst.
      unfold LLVMParamsBigIntptr.PTOI.ptr_to_int, fst.
      rewrite memory_stack_memory_mem_state_memory.
      destruct m_fin.
      destruct ms_memory_stack.
      cbn in READ_RAW; cbn.
      erewrite read_byte_raw_lifted_fin_inf; eauto.
      cbn.
      rewrite MemoryBigIntptrInfiniteSpec.LP.PROV.access_allowed_refl.
      split; auto.
    }

    pose proof RBP_INF as RBP_FIN.
    apply RBP in RBP_FIN.

    assert (InfMem.MMEP.MemSpec.read_byte_allowed (lift_MemState m_fin) ptr_inf) as ALLOWED_INF.
    {
      red.
      exists aid.
      split.
      - repeat red.
        exists (lift_MemState m_fin). exists true.
        split; [|cbn; auto].

        repeat red.
        split.
        + repeat red.
          exists (InfMem.MMEP.MMSP.MemState_get_memory (lift_MemState m_fin)).
          exists (InfMem.MMEP.MMSP.MemState_get_memory (lift_MemState m_fin)).
          split; cbn; auto.
          rewrite memory_stack_memory_mem_state_memory.
          subst; cbn.
          destruct m_fin, ms_memory_stack.
          cbn; cbn in READ_RAW.
          erewrite read_byte_raw_lifted_fin_inf; eauto.
          split; auto.
          apply MemoryBigIntptrInfiniteSpec.LP.PROV.aid_eq_dec_refl.
        + intros ms' x H.
          cbn in H.
          inv H.
          auto.
      - subst; cbn.
        apply MemoryBigIntptrInfiniteSpec.LP.PROV.access_allowed_refl.
    }

    pose proof ALLOWED_INF as ALLOWED_FIN.
    apply ALLOWED in ALLOWED_FIN.

    repeat red in RBP_FIN.
    destruct RBP_FIN as (sab&a&MS&RBP_FIN).
    destruct MS; subst.
    break_match_hyp.
    2: {
      destruct ALLOWED_FIN as (aid'&ALLOCATED&ACCESS).
      repeat red in ALLOCATED.
      destruct ALLOCATED as (sab&a&ALLOCATED&ASSERT).
      cbn in ASSERT. destruct ASSERT; subst.
      repeat red in ALLOCATED.
      destruct ALLOCATED as [ALLOCATED _].
      repeat red in ALLOCATED.
      destruct ALLOCATED as (sab&a&MS&ALLOCATED).
      destruct MS; subst.

      rewrite Heqo in ALLOCATED.
      cbn in ALLOCATED.
      destruct ALLOCATED; discriminate.
    }

    destruct m.

    destruct ALLOWED_FIN as (aid'&ALLOCATED&ACCESS).
    repeat red in ALLOCATED.
    destruct ALLOCATED as (sab&a'&ALLOCATED&ASSERT).
    cbn in ASSERT. destruct ASSERT; subst.
    repeat red in ALLOCATED.
    destruct ALLOCATED as [ALLOCATED _].
    repeat red in ALLOCATED.
    destruct ALLOCATED as (sab&a'&MS&ALLOCATED).
    destruct MS; subst.

    rewrite Heqo in ALLOCATED.
    cbn in ALLOCATED.
    destruct ALLOCATED.

    cbn in RBP_FIN.
    cbn in ACCESS.

    destruct (LLVMParamsBigIntptr.PROV.aid_eq_dec aid' a); try discriminate; subst.
    rewrite ACCESS in RBP_FIN.
    destruct RBP_FIN; subst.

    cbn in Heqo.
    rewrite memory_stack_memory_mem_state_memory in Heqo.
    rewrite Heqo.

    (* TODO: need to show that aid = aid'...

       This should be true, but need a lemma about access_allowed and
       allocation_id_to_prov to do this...

       In this case there should only be one provenance in the Prov
       argument to access_allowed, so aid' must = aid.
     *)
    assert (a = aid) by admit.
    subst.
    auto.
  Admitted.

  (* TODO: Some tricky IntMap reasoning *)
  Lemma fin_inf_read_byte_raw_None :
    forall m_inf m_fin ptr,
      MemState_refine_prop m_inf m_fin ->
      Memory64BitIntptr.MMEP.MMSP.read_byte_raw
        (Memory64BitIntptr.MMEP.MMSP.mem_state_memory m_fin)
        ptr = None ->
      MemoryBigIntptr.MMEP.MMSP.read_byte_raw
        (MemoryBigIntptr.MMEP.MMSP.mem_state_memory m_inf)
        ptr = None.
  Proof.
    intros m_inf m_fin ptr MSR READ.
    Transparent Memory64BitIntptr.MMEP.MMSP.read_byte_raw.
    Transparent MemoryBigIntptr.MMEP.MMSP.read_byte_raw.
    unfold Memory64BitIntptr.MMEP.MMSP.read_byte_raw in READ.
    unfold MemoryBigIntptr.MMEP.MMSP.read_byte_raw.

    Opaque Memory64BitIntptr.MMEP.MMSP.read_byte_raw.
    Opaque MemoryBigIntptr.MMEP.MMSP.read_byte_raw.
  Admitted.

  (* TODO: Some tricky IntMap reasoning *)
  Lemma inf_fin_read_byte_raw_None :
    forall m_inf m_fin ptr,
      MemState_refine_prop m_inf m_fin ->
      MemoryBigIntptr.MMEP.MMSP.read_byte_raw
        (MemoryBigIntptr.MMEP.MMSP.mem_state_memory m_inf)
        ptr = None ->
      Memory64BitIntptr.MMEP.MMSP.read_byte_raw
        (Memory64BitIntptr.MMEP.MMSP.mem_state_memory m_fin)
        ptr = None.
  Proof.
    intros m_inf m_fin ptr CONV READ.
    Transparent Memory64BitIntptr.MMEP.MMSP.read_byte_raw.
    Transparent MemoryBigIntptr.MMEP.MMSP.read_byte_raw.
    unfold Memory64BitIntptr.MMEP.MMSP.read_byte_raw in READ.
    unfold MemoryBigIntptr.MMEP.MMSP.read_byte_raw.

    Opaque Memory64BitIntptr.MMEP.MMSP.read_byte_raw.
    Opaque MemoryBigIntptr.MMEP.MMSP.read_byte_raw.
  Admitted.

  Lemma read_byte_raw_fin_addr :
    forall {m_inf m_fin addr byte_fin aid},
      MemState_refine_prop m_inf m_fin ->
      Memory64BitIntptr.MMEP.MMSP.read_byte_raw (Memory64BitIntptr.MMEP.MMSP.mem_state_memory m_fin) addr = Some (byte_fin, aid) ->
      (forall pr, exists ptr, FinITOP.int_to_ptr addr pr = NoOom ptr).
  Proof.
  Admitted.

  Lemma addr_allocated_fin_addr :
    forall {m_inf m_inf' m_fin addr_inf aid},
      MemState_refine_prop m_inf m_fin ->
      MemoryBigIntptr.MMEP.MMSP.addr_allocated_prop addr_inf aid (InfMem.MMEP.MMSP.MemState_get_memory m_inf) (ret (m_inf', true)) ->
      (forall pr, exists ptr, FinITOP.int_to_ptr (InfPTOI.ptr_to_int addr_inf) pr = NoOom ptr).
  Proof.
  Admitted.

  (* TODO: Prove this *)
  Lemma inf_fin_read_byte_raw :
    forall {m_inf m_fin addr byte_inf aid},
      MemState_refine_prop m_inf m_fin ->
      MemoryBigIntptr.MMEP.MMSP.read_byte_raw (MemoryBigIntptrInfiniteSpec.MMSP.mem_state_memory m_inf) addr = Some (byte_inf, aid) ->
      exists byte_fin,
        Memory64BitIntptr.MMEP.MMSP.read_byte_raw (Memory64BitIntptr.MMEP.MMSP.mem_state_memory m_fin) addr = Some (byte_fin, aid) /\
          sbyte_refine byte_inf byte_fin.
  Proof.
    intros m_inf m_fin addr byte_inf aid MSR READ_RAW.
    destruct MSR.
    destruct H0.
    clear H1 H.
    destruct H0 as [ALLOWED RBP].
    unfold InfMem.MMEP.MemSpec.read_byte_prop_all_preserved in RBP.
    remember (addr, MemoryBigIntptrInfiniteSpec.LP.PROV.allocation_id_to_prov aid) as ptr_inf.
    specialize (RBP ptr_inf byte_inf).
    specialize (ALLOWED ptr_inf).

    assert (InfMem.MMEP.MemSpec.read_byte_prop m_inf ptr_inf byte_inf) as RBP_INF.
    {
      repeat red.
      exists (InfMem.MMEP.MMSP.MemState_get_memory m_inf).
      exists (InfMem.MMEP.MMSP.MemState_get_memory m_inf).

      split.
      cbn; auto.

      subst.
      unfold LLVMParamsBigIntptr.PTOI.ptr_to_int, fst.
      rewrite memory_stack_memory_mem_state_memory.
      rewrite READ_RAW.
      cbn.
      rewrite MemoryBigIntptrInfiniteSpec.LP.PROV.access_allowed_refl.
      split; auto.
    }

    pose proof RBP_INF as RBP_FIN.
    apply RBP in RBP_FIN.

    assert (InfMem.MMEP.MemSpec.read_byte_allowed m_inf ptr_inf) as ALLOWED_INF.
    {
      red.
      exists aid.
      split.
      - repeat red.
        exists m_inf. exists true.
        split; [|cbn; auto].

        repeat red.
        split.
        + repeat red.
          exists (InfMem.MMEP.MMSP.MemState_get_memory m_inf).
          exists (InfMem.MMEP.MMSP.MemState_get_memory m_inf).
          split; cbn; auto.
          rewrite memory_stack_memory_mem_state_memory.
          subst; cbn.
          rewrite READ_RAW.
          split; auto.
          apply MemoryBigIntptrInfiniteSpec.LP.PROV.aid_eq_dec_refl.
        + intros ms' x H.
          cbn in H.
          inv H.
          auto.
      - subst; cbn.
        apply MemoryBigIntptrInfiniteSpec.LP.PROV.access_allowed_refl.
    }

    pose proof ALLOWED_INF as ALLOWED_FIN.
    apply ALLOWED in ALLOWED_FIN.

    (* Because of RBP I know I can read a byte_inf from (lift_MemState
       m_fin)... The original, unlifted byte is the byte_fin that I need
       to supply to the existential. *)
    repeat red in RBP_INF.
    repeat red in RBP_FIN.
    destruct RBP_FIN as (sab&a&MS&RBP_FIN).
    destruct MS; subst.
    destruct RBP_INF as (sab&a&MS&RBP_INF).
    destruct MS; subst.
    cbn in RBP_FIN, RBP_INF.
    rewrite memory_stack_memory_mem_state_memory, READ_RAW in RBP_INF.
    cbn in RBP_INF.
    rewrite MemoryBigIntptrInfiniteSpec.LP.PROV.access_allowed_refl in RBP_INF.

    assert (exists s aid', InfMem.MMEP.MMSP.read_byte_raw
                        (InfMem.MMEP.MMSP.memory_stack_memory
                           (InfMem.MMEP.MMSP.MemState_get_memory (lift_MemState m_fin)))
                        addr = Some (s, aid') /\
                        LLVMParamsBigIntptr.PROV.access_allowed
                          (MemoryBigIntptrInfiniteSpec.LP.PROV.allocation_id_to_prov aid) aid' = true) as [byte_fin_lifted [aid' [READ_BYTE_FIN_LIFTED ACCESS_ALLOWED_BYTE_FIN_LIFTED]]].
    {
      clear - ALLOWED_FIN.
      red in ALLOWED_FIN.
      destruct ALLOWED_FIN as (aid'&ALLOCATED&ACCESS).
      repeat red in ALLOCATED.
      destruct ALLOCATED as (sab&a&ALLOCATED&ASSERT).
      cbn in ASSERT. destruct ASSERT; subst.
      repeat red in ALLOCATED.
      destruct ALLOCATED as [ALLOCATED _].
      repeat red in ALLOCATED.
      destruct ALLOCATED as (sab&a&MS&ALLOCATED).
      destruct MS; subst.

      cbn in ALLOCATED.
      break_match_hyp.
      2: {
        destruct ALLOCATED; discriminate.
      }

      destruct m.
      cbn in ACCESS.
      exists s. exists a.
      split; auto.
      destruct ALLOCATED.
      destruct (LLVMParamsBigIntptr.PROV.aid_eq_dec aid' a); inv H0.
      auto.
    }

    rewrite READ_BYTE_FIN_LIFTED in RBP_FIN.
    cbn in RBP_FIN.
    rewrite ACCESS_ALLOWED_BYTE_FIN_LIFTED in RBP_FIN.
    destruct RBP_FIN; subst.

    apply read_byte_raw_lifted.
    (* TODO: need to show that aid = aid'...

       This should be true, but need a lemma about access_allowed and
       allocation_id_to_prov to do this...

       In this case there should only be one provenance in the Prov
       argument to access_allowed, so aid' must = aid.
     *)
    assert (aid = aid') by admit.
    subst.

    rewrite memory_stack_memory_mem_state_memory in READ_BYTE_FIN_LIFTED.
    destruct m_fin. destruct ms_memory_stack.
    cbn in *.
    auto.
  Admitted.

  (* TODO: Maybe swap MemState for memory_stack to get rid of MemState_get_memory *)
  Lemma fin_inf_addr_allocated_prop :
    forall addr_fin addr_inf ms_fin ms_inf aid,
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      Memory64BitIntptr.MMEP.MMSP.addr_allocated_prop addr_fin aid
        (FinMem.MMEP.MMSP.MemState_get_memory ms_fin)
        (success_unERR_UB_OOM (FinMem.MMEP.MMSP.MemState_get_memory ms_fin, true)) ->
      MemoryBigIntptr.MMEP.MMSP.addr_allocated_prop addr_inf aid
        (InfMem.MMEP.MMSP.MemState_get_memory ms_inf)
        (success_unERR_UB_OOM (InfMem.MMEP.MMSP.MemState_get_memory ms_inf, true)).
  Proof.
    intros addr_fin addr_inf ms_fin ms_inf aid MSR ADDR_CONV ALLOCATED.
    repeat red.
    exists (InfMem.MMEP.MMSP.MemState_get_memory ms_inf).
    exists (InfMem.MMEP.MMSP.MemState_get_memory ms_inf).
    split; [cbn; auto|].
    destruct ALLOCATED as [mst_fin [mst_fin' [[MST MST'] ALLOCATED]]]; subst.

    break_match_hyp.
    2: {
      destruct ALLOCATED; discriminate.
    }

    destruct m.
    cbn in ALLOCATED.

    eapply fin_inf_read_byte_raw in Heqo; eauto.
    erewrite fin_inf_ptoi in Heqo; eauto.
    rewrite memory_stack_memory_mem_state_memory.
    rewrite Heqo.

    destruct ALLOCATED.
    split; auto.

    destruct (LLVMParams64BitIntptr.PROV.aid_eq_dec aid a); cbn in *; try discriminate; subst.
    destruct (LLVMParamsBigIntptr.PROV.aid_eq_dec a a); cbn in *; try contradiction; auto.
  Qed.

  Lemma inf_fin_addr_allocated_prop :
    forall addr_fin addr_inf ms_fin ms_inf aid,
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      MemoryBigIntptr.MMEP.MMSP.addr_allocated_prop addr_inf aid
        (InfMem.MMEP.MMSP.MemState_get_memory ms_inf)
        (success_unERR_UB_OOM (InfMem.MMEP.MMSP.MemState_get_memory ms_inf, true)) ->
      Memory64BitIntptr.MMEP.MMSP.addr_allocated_prop addr_fin aid
        (FinMem.MMEP.MMSP.MemState_get_memory ms_fin)
        (success_unERR_UB_OOM (FinMem.MMEP.MMSP.MemState_get_memory ms_fin, true)).
  Proof.
    intros addr_fin addr_inf ms_fin ms_inf aid MSR ADDR_CONV ALLOCATED.
    cbn in *.
    destruct ALLOCATED as [mst_inf [mst_inf' [[MST MST'] ALLOCATED]]]; subst.
    exists (FinMem.MMEP.MMSP.MemState_get_memory ms_fin).
    exists (FinMem.MMEP.MMSP.MemState_get_memory ms_fin).
    split; auto.
    break_match_hyp; cbn in *.
    2: {
      destruct ALLOCATED.
      discriminate.
    }

    destruct m as [byte_inf aid'].
    epose proof inf_fin_read_byte_raw MSR Heqo as [byte_fin [READ_FIN BYTE_REF]].
    erewrite fin_inf_ptoi; eauto.
    rewrite memory_stack_memory_mem_state_memory_fin.
    rewrite READ_FIN.

    split; auto.
    destruct ALLOCATED; auto.

    destruct (LLVMParamsBigIntptr.PROV.aid_eq_dec aid aid'); inv H0.
    apply LLVMParams64BitIntptr.PROV.aid_eq_dec_refl.
  Qed.

  Lemma inf_fin_addr_allocated_prop_exists :
    forall {addr_inf ms_fin ms_inf aid},
      MemState_refine_prop ms_inf ms_fin ->
      MemoryBigIntptr.MMEP.MMSP.addr_allocated_prop addr_inf aid
        (InfMem.MMEP.MMSP.MemState_get_memory ms_inf)
        (success_unERR_UB_OOM (InfMem.MMEP.MMSP.MemState_get_memory ms_inf, true)) ->
      exists addr_fin,
        InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin /\
        Memory64BitIntptr.MMEP.MMSP.addr_allocated_prop addr_fin aid
          (FinMem.MMEP.MMSP.MemState_get_memory ms_fin)
          (success_unERR_UB_OOM (FinMem.MMEP.MMSP.MemState_get_memory ms_fin, true)).
  Proof.
    intros addr_inf ms_fin ms_inf aid MSR ALLOCATED.
    repeat red in ALLOCATED.
    destruct ALLOCATED as [ms_inf' [ms_inf'' [[MST MST'] ALLOCATED]]]; subst.

    break_match_hyp.
    2: {
      cbn in *. destruct ALLOCATED; discriminate.
    }

    destruct m.

    epose proof inf_fin_read_byte_raw MSR Heqo.
    destruct H as (byte_fin&READ_FIN&BYTE_REF).
    destruct addr_inf.
    cbn in *.

    pose proof read_byte_raw_fin_addr MSR READ_FIN p as [ptr CONV].
    exists ptr. split; auto.
    exists (FinMem.MMEP.MMSP.MemState_get_memory ms_fin).
    exists (FinMem.MMEP.MMSP.MemState_get_memory ms_fin).
    split; auto.

    erewrite FinLP.ITOP.ptr_to_int_int_to_ptr; eauto.
    rewrite memory_stack_memory_mem_state_memory_fin.
    rewrite READ_FIN.

    split; auto.
    destruct ALLOCATED; auto.

    destruct (LLVMParamsBigIntptr.PROV.aid_eq_dec aid a); inv H0.
    apply LLVMParams64BitIntptr.PROV.aid_eq_dec_refl.
  Qed.

  Lemma MemState_refine_convert_memory_stack :
    forall ms_inf ms_fin,
      MemState_refine ms_inf ms_fin ->
      convert_memory_stack (MemoryBigIntptr.MMEP.MMSP.MemState_get_memory ms_inf) = NoOom (Memory64BitIntptr.MMEP.MMSP.MemState_get_memory ms_fin).
  Proof.
    intros ms_inf ms_fin REF.
    destruct ms_inf; cbn in *.
    unfold MemState_refine in REF.
    cbn in *.
    break_match_hyp; inv REF.
    cbn.
    reflexivity.
  Qed.

  Lemma MemState_refine_convert_memory :
    forall ms_inf ms_fin,
      MemState_refine ms_inf ms_fin ->
      convert_memory (MemoryBigIntptr.MMEP.MMSP.mem_state_memory ms_inf) = NoOom (Memory64BitIntptr.MMEP.MMSP.mem_state_memory ms_fin).
  Proof.
    intros ms_inf ms_fin REF.
    destruct ms_inf; cbn in *.
    unfold MemState_refine in REF.
    cbn in *.
    break_match_hyp; inv REF.
    destruct ms_memory_stack; cbn in *.
    destruct memory_stack_memory; cbn in *.
    break_match_hyp; inv Heqo.
    break_match_hyp; inv H0.
    break_match_hyp; inv H1.
    break_match_hyp; inv Heqo1.
    cbn in *.
    reflexivity.
  Qed.

  Lemma MemState_refine_convert_memory' :
    forall ms_inf ms_fin,
      MemState_refine ms_inf ms_fin ->
      convert_memory (MemoryBigIntptr.MMEP.MMSP.memory_stack_memory
                        (MemoryBigIntptr.MMEP.MMSP.MemState_get_memory ms_inf)) = NoOom (Memory64BitIntptr.MMEP.MMSP.memory_stack_memory
                                                                                           (Memory64BitIntptr.MMEP.MMSP.MemState_get_memory ms_fin)).
  Proof.
    intros ms_inf ms_fin REF.
    destruct ms_inf; cbn in *.
    unfold MemState_refine in REF.
    cbn in *.
    break_match_hyp; inv REF.
    destruct ms_memory_stack; cbn in *.
    destruct memory_stack_memory; cbn in *.
    break_match_hyp; inv Heqo.
    break_match_hyp; inv H0.
    break_match_hyp; inv H1.
    break_match_hyp; inv Heqo1.
    cbn in *.
    reflexivity.
  Qed.

  Lemma fin_inf_byte_allocated_MemPropT :
    forall addr_fin addr_inf ms_fin ms_inf aid,
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      Memory64BitIntptr.MMEP.MemSpec.byte_allocated_MemPropT addr_fin aid ms_fin (ret (ms_fin, tt)) ->
      MemoryBigIntptr.MMEP.MemSpec.byte_allocated_MemPropT addr_inf aid ms_inf (ret (ms_inf, tt)).
  Proof.
    intros addr_fin addr_inf ms_fin ms_inf aid MSR ADDR_CONV ALLOCATED.
    red; red in ALLOCATED.
    Opaque Memory64BitIntptr.MMEP.MMSP.addr_allocated_prop.
    Opaque MemoryBigIntptr.MMEP.MMSP.addr_allocated_prop.
    cbn in *.
    destruct ALLOCATED as [ms_fin' [res [ALLOCATED [MS RES]]]]; subst.
    exists ms_inf. exists true.
    split; auto.
    red.
    destruct ALLOCATED.
    split.
    - eapply fin_inf_addr_allocated_prop; eauto.
    - intros ms' x H1.
      cbn in *.
      inv H1.
      auto.
  Qed.

  Lemma addr_convert_fin_to_inf_addr :
    forall addr_fin,
      InfToFinAddrConvert.addr_convert (fin_to_inf_addr addr_fin) = NoOom addr_fin.
  Proof.
    intros addr_fin.
    unfold fin_to_inf_addr in *.
    destruct (FinToInfAddrConvertSafe.addr_convert_succeeds addr_fin).
    apply FinToInfAddrConvertSafe.addr_convert_safe in e.
    auto.
  Qed.

  Lemma fin_inf_byte_allocated_MemPropT_exists :
    forall addr_fin ms_fin ms_inf aid,
      MemState_refine_prop ms_inf ms_fin ->
      Memory64BitIntptr.MMEP.MemSpec.byte_allocated_MemPropT addr_fin aid ms_fin (ret (ms_fin, tt)) ->
      exists addr_inf,
        InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin /\
          MemoryBigIntptr.MMEP.MemSpec.byte_allocated_MemPropT addr_inf aid ms_inf (ret (ms_inf, tt)).
  Proof.
    intros addr_fin ms_fin ms_inf aid MSR ALLOCATED.
    pose proof addr_convert_fin_to_inf_addr addr_fin.
    exists (fin_to_inf_addr addr_fin).
    split; auto.
    eapply fin_inf_byte_allocated_MemPropT; eauto.
  Qed.

  Lemma inf_fin_byte_allocated_MemPropT :
    forall addr_fin addr_inf ms_fin ms_inf aid,
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      MemoryBigIntptr.MMEP.MemSpec.byte_allocated_MemPropT addr_inf aid ms_inf (ret (ms_inf, tt)) ->
      Memory64BitIntptr.MMEP.MemSpec.byte_allocated_MemPropT addr_fin aid ms_fin (ret (ms_fin, tt)).
  Proof.
    intros addr_fin addr_inf ms_fin ms_inf aid MSR ADDR_CONV ALLOCATED.
    red; red in ALLOCATED.
    Opaque Memory64BitIntptr.MMEP.MMSP.addr_allocated_prop.
    Opaque MemoryBigIntptr.MMEP.MMSP.addr_allocated_prop.
    cbn in *.
    destruct ALLOCATED as [ms_fin' [res [ALLOCATED [MS RES]]]]; subst.
    exists ms_fin. exists true.
    split; auto.
    red.
    destruct ALLOCATED.
    split.
    - eapply inf_fin_addr_allocated_prop; eauto.
    - intros ms' x H1.
      cbn in *.
      inv H1.
      auto.
  Qed.

  Lemma inf_fin_byte_allocated_MemPropT_exists :
    forall addr_inf ms_fin ms_inf aid,
      MemState_refine_prop ms_inf ms_fin ->
      MemoryBigIntptr.MMEP.MemSpec.byte_allocated_MemPropT addr_inf aid ms_inf (ret (ms_inf, tt)) ->
      exists addr_fin,
        InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin /\
        Memory64BitIntptr.MMEP.MemSpec.byte_allocated_MemPropT addr_fin aid ms_fin (ret (ms_fin, tt)).
  Proof.
    intros addr_inf ms_fin ms_inf aid MSR ALLOCATED.
    red in ALLOCATED.
    unfold Memory64BitIntptr.MMEP.MemSpec.byte_allocated_MemPropT.
    Opaque Memory64BitIntptr.MMEP.MMSP.addr_allocated_prop.
    Opaque MemoryBigIntptr.MMEP.MMSP.addr_allocated_prop.
    repeat red in ALLOCATED.
    destruct ALLOCATED as [ms_fin' [res [ALLOCATED [MS RES]]]]; subst.
    red in ALLOCATED.
    cbn in *.
    destruct ALLOCATED.

    pose proof addr_allocated_fin_addr MSR H (InfPROV.address_provenance addr_inf) as [ptr RAW_CONV].
    assert (InfToFinAddrConvert.addr_convert addr_inf = NoOom ptr) as CONV.
    {
      unfold InfToFinAddrConvert.addr_convert. destruct addr_inf. cbn in *. auto.
    }

    exists ptr.
    split; auto.

    exists ms_fin.
    exists true.
    split; auto.
    red.
    split.
    eapply inf_fin_addr_allocated_prop; eauto.

    intros ms' x0 H3.
    cbn in *.
    inv H3.
    auto.
  Qed.

  Lemma fin_inf_byte_allocated :
    forall addr_fin addr_inf ms_fin ms_inf aid,
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      Memory64BitIntptr.MMEP.MemSpec.byte_allocated ms_fin addr_fin aid ->
      MemoryBigIntptr.MMEP.MemSpec.byte_allocated ms_inf addr_inf aid.
  Proof.
    intros addr_fin addr_inf ms_fin ms_inf aid MSR ADDR_CONV ALLOCATED.
    red; red in ALLOCATED.
    eapply fin_inf_byte_allocated_MemPropT; eauto.
  Qed.

  Lemma fin_inf_byte_allocated_exists :
    forall addr_fin ms_fin ms_inf aid,
      MemState_refine_prop ms_inf ms_fin ->
      Memory64BitIntptr.MMEP.MemSpec.byte_allocated ms_fin addr_fin aid ->
      exists addr_inf,
        InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin /\
          MemoryBigIntptr.MMEP.MemSpec.byte_allocated ms_inf addr_inf aid.
  Proof.
    intros addr_fin ms_fin ms_inf aid MSR ALLOCATED.
    eapply fin_inf_byte_allocated_MemPropT_exists; eauto.
  Qed.

  Lemma inf_fin_byte_allocated :
    forall addr_fin addr_inf ms_fin ms_inf aid,
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      MemoryBigIntptr.MMEP.MemSpec.byte_allocated ms_inf addr_inf aid ->
      Memory64BitIntptr.MMEP.MemSpec.byte_allocated ms_fin addr_fin aid.
  Proof.
    intros addr_fin addr_inf ms_fin ms_inf aid MSR ADDR_CONV ALLOCATED.
    red; red in ALLOCATED.
    eapply inf_fin_byte_allocated_MemPropT; eauto.
  Qed.

  Lemma inf_fin_byte_allocated_exists :
    forall addr_inf ms_fin ms_inf aid,
      MemState_refine_prop ms_inf ms_fin ->
      MemoryBigIntptr.MMEP.MemSpec.byte_allocated ms_inf addr_inf aid ->
      exists addr_fin,
        InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin /\
        Memory64BitIntptr.MMEP.MemSpec.byte_allocated ms_fin addr_fin aid.
  Proof.
    intros addr_inf ms_fin ms_inf aid MSR ALLOCATED.
    red in ALLOCATED.
    eapply inf_fin_byte_allocated_MemPropT_exists; eauto.
  Qed.

  Lemma fin_inf_byte_not_allocated :
    forall addr_fin addr_inf ms_fin ms_inf,
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      Memory64BitIntptr.MMEP.MemSpec.byte_not_allocated ms_fin addr_fin ->
      MemoryBigIntptr.MMEP.MemSpec.byte_not_allocated ms_inf addr_inf.
  Proof.
    intros addr_fin addr_inf ms_fin ms_inf MSR ADDR_CONV NALLOCATED.
    red; red in NALLOCATED.
    intros aid ALLOCATED.
    eapply inf_fin_byte_allocated in ALLOCATED; eauto.
    eapply NALLOCATED; eauto.
  Qed.

  Lemma inf_fin_byte_not_allocated :
    forall addr_fin addr_inf ms_fin ms_inf,
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      MemoryBigIntptr.MMEP.MemSpec.byte_not_allocated ms_inf addr_inf ->
      Memory64BitIntptr.MMEP.MemSpec.byte_not_allocated ms_fin addr_fin.
  Proof.
    intros addr_fin addr_inf ms_fin ms_inf MSR ADDR_CONV NALLOCATED.
    red; red in NALLOCATED.
    intros aid ALLOCATED.
    eapply fin_inf_byte_allocated in ALLOCATED; eauto.
    eapply NALLOCATED; eauto.
  Qed.

  Lemma inf_fin_big_address_byte_not_allocated :
    forall {addr_inf ms_fin ms_inf msg},
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert addr_inf = Oom msg ->
      MemoryBigIntptr.MMEP.MemSpec.byte_not_allocated ms_inf addr_inf.
  Proof.
    intros addr_inf ms_fin ms_inf msg MSR ADDR_CONV aid ALLOCATED.
    eapply inf_fin_byte_allocated_exists in ALLOCATED; eauto.
    destruct ALLOCATED as (?&?&?).
    rewrite ADDR_CONV in H.
    discriminate.
  Qed.

  Lemma fin_inf_access_allowed :
    forall addr_fin addr_inf aid res,
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      LLVMParams64BitIntptr.PROV.access_allowed
        (LLVMParams64BitIntptr.PROV.address_provenance addr_fin) aid = res ->
      LLVMParamsBigIntptr.PROV.access_allowed (LLVMParamsBigIntptr.PROV.address_provenance addr_inf) aid = res.
  Proof.
    intros addr_fin addr_inf aid res ADDR_CONV ACCESS.
    destruct addr_inf.
    cbn in *.
    pose proof ITOP.int_to_ptr_provenance _ _ _ ADDR_CONV. subst.
    unfold LLVMParams64BitIntptr.PROV.access_allowed in *.
    unfold LLVMParamsBigIntptr.PROV.access_allowed in *.

    (* TODO: Need to expose access_allowed *)
    admit.
  Admitted.

  Lemma inf_fin_access_allowed :
    forall addr_fin addr_inf aid res,
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      LLVMParamsBigIntptr.PROV.access_allowed
        (LLVMParamsBigIntptr.PROV.address_provenance addr_inf) aid = res ->
      LLVMParams64BitIntptr.PROV.access_allowed
        (LLVMParams64BitIntptr.PROV.address_provenance addr_fin) aid = res.
  Proof.
    intros addr_fin addr_inf aid res ADDR_CONV ACCESS.
    destruct addr_inf.
    cbn in *.
    pose proof ITOP.int_to_ptr_provenance _ _ _ ADDR_CONV. subst.
    unfold LLVMParams64BitIntptr.PROV.access_allowed in *.
    unfold LLVMParamsBigIntptr.PROV.access_allowed in *.

    (* TODO: Need to expose access_allowed *)
    admit.
  Admitted.

  Lemma fin_inf_read_byte_allowed :
    forall addr_fin addr_inf ms_fin ms_inf,
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      Memory64BitIntptr.MMEP.MemSpec.read_byte_allowed ms_fin addr_fin ->
      MemoryBigIntptr.MMEP.MemSpec.read_byte_allowed ms_inf addr_inf.
  Proof.
    intros addr_fin addr_inf ms_fin ms_inf MSR ADDR_CONV READ_ALLOWED.
    red. red in READ_ALLOWED.

    destruct READ_ALLOWED as [aid [BYTE_ALLOCATED ACCESS_ALLOWED]].
    exists aid.
    split.
    - eapply fin_inf_byte_allocated; eauto.
    - eapply fin_inf_access_allowed; eauto.
  Qed.

  Lemma inf_fin_read_byte_allowed :
    forall addr_fin addr_inf ms_fin ms_inf,
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      MemoryBigIntptr.MMEP.MemSpec.read_byte_allowed ms_inf addr_inf ->
      Memory64BitIntptr.MMEP.MemSpec.read_byte_allowed ms_fin addr_fin.
  Proof.
    intros addr_fin addr_inf ms_fin ms_inf MSR ADDR_CONV READ_ALLOWED.
    red. red in READ_ALLOWED.

    destruct READ_ALLOWED as [aid [BYTE_ALLOCATED ACCESS_ALLOWED]].
    exists aid.
    split.
    - eapply inf_fin_byte_allocated; eauto.
    - eapply inf_fin_access_allowed; eauto.
  Qed.

  Lemma fin_inf_write_byte_allowed :
    forall addr_fin addr_inf ms_fin ms_inf,
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      Memory64BitIntptr.MMEP.MemSpec.write_byte_allowed ms_fin addr_fin ->
      MemoryBigIntptr.MMEP.MemSpec.write_byte_allowed ms_inf addr_inf.
  Proof.
    intros addr_fin addr_inf ms_fin ms_inf MSR ADDR_CONV WRITE_ALLOWED.
    red. red in WRITE_ALLOWED.

    destruct WRITE_ALLOWED as [aid [BYTE_ALLOCATED ACCESS_ALLOWED]].
    exists aid.
    split.
    - eapply fin_inf_byte_allocated; eauto.
    - eapply fin_inf_access_allowed; eauto.
  Qed.

  Lemma inf_fin_write_byte_allowed :
    forall addr_fin addr_inf ms_fin ms_inf,
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      MemoryBigIntptr.MMEP.MemSpec.write_byte_allowed ms_inf addr_inf ->
      Memory64BitIntptr.MMEP.MemSpec.write_byte_allowed ms_fin addr_fin.
  Proof.
    intros addr_fin addr_inf ms_fin ms_inf MSR ADDR_CONV WRITE_ALLOWED.
    red. red in WRITE_ALLOWED.

    destruct WRITE_ALLOWED as [aid [BYTE_ALLOCATED ACCESS_ALLOWED]].
    exists aid.
    split.
    - eapply inf_fin_byte_allocated; eauto.
    - eapply inf_fin_access_allowed; eauto.
  Qed.

  Lemma fin_inf_free_byte_allowed :
    forall addr_fin addr_inf ms_fin ms_inf,
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      Memory64BitIntptr.MMEP.MemSpec.free_byte_allowed ms_fin addr_fin ->
      MemoryBigIntptr.MMEP.MemSpec.free_byte_allowed ms_inf addr_inf.
  Proof.
    intros addr_fin addr_inf ms_fin ms_inf MSR ADDR_CONV FREE_ALLOWED.
    red. red in FREE_ALLOWED.

    destruct FREE_ALLOWED as [aid [BYTE_ALLOCATED ACCESS_ALLOWED]].
    exists aid.
    split.
    - eapply fin_inf_byte_allocated; eauto.
    - eapply fin_inf_access_allowed; eauto.
  Qed.

  Lemma inf_fin_free_byte_allowed :
    forall addr_fin addr_inf ms_fin ms_inf,
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      MemoryBigIntptr.MMEP.MemSpec.free_byte_allowed ms_inf addr_inf ->
      Memory64BitIntptr.MMEP.MemSpec.free_byte_allowed ms_fin addr_fin.
  Proof.
    intros addr_fin addr_inf ms_fin ms_inf MSR ADDR_CONV FREE_ALLOWED.
    red. red in FREE_ALLOWED.

    destruct FREE_ALLOWED as [aid [BYTE_ALLOCATED ACCESS_ALLOWED]].
    exists aid.
    split.
    - eapply inf_fin_byte_allocated; eauto.
    - eapply inf_fin_access_allowed; eauto.
  Qed.


  Lemma fin_inf_read_byte_prop_MemPropT :
    forall addr_fin addr_inf ms_fin ms_inf byte_inf byte_fin,
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      sbyte_refine byte_inf byte_fin ->
      Memory64BitIntptr.MMEP.MMSP.read_byte_MemPropT addr_fin
        (Memory64BitIntptr.MMEP.MMSP.MemState_get_memory ms_fin)
        (ret (Memory64BitIntptr.MMEP.MMSP.MemState_get_memory ms_fin, byte_fin)) ->
      MemoryBigIntptr.MMEP.MMSP.read_byte_MemPropT addr_inf
        (MemoryBigIntptr.MMEP.MMSP.MemState_get_memory ms_inf)
        (ret (MemoryBigIntptr.MMEP.MMSP.MemState_get_memory ms_inf, byte_inf)).
  Proof.
    intros addr_fin addr_inf ms_fin ms_inf byte_inf byte_fin MSR ADDR_CONV BYTE_REF RBP.
    (* TODO: make things opaque? *)
    destruct RBP as [ms_fin' [ms_fin'' [[MS MS'] READ]]].
    subst.
    destruct ms_fin eqn:MSFIN. cbn in READ.
    destruct ms_inf eqn:MSINF.
    break_match_hyp.
    (* read_byte_MemPropT may have UB... Which
                           means sbyte_refine byte_inf byte_fin might not
                           hold because byte_fin could be any byte.
     *)
    - assert (byte_inf = lift_SByte byte_fin) as BYTE'.
      { clear - BYTE_REF.
        red in BYTE_REF.
        erewrite lift_SByte_convert_SByte_inverse; eauto.
      }
      subst.

      destruct m.
      epose proof fin_inf_read_byte_raw MSR Heqo.

      cbn.
      eexists. eexists.
      split; eauto.
      erewrite fin_inf_ptoi in H; eauto.
      destruct ms_memory_stack0.
      cbn; cbn in H.
      rewrite H.
      erewrite fin_inf_access_allowed; cbn; eauto.
      break_match_goal; cbn; eauto.

      break_match_hyp.
      destruct READ; subst; auto.

      cbn in Heqb0.
      rewrite Heqb0 in Heqb.
      discriminate.
    - epose proof fin_inf_read_byte_raw_None _ _ _ MSR Heqo.
      cbn.
      eexists. eexists.
      split; eauto.
      erewrite fin_inf_ptoi in H; eauto.
      destruct ms_memory_stack0; cbn in *.
      rewrite H.
      auto.
  Qed.

  Lemma fin_to_inf_uvalue_injective :
    forall uv1 uv2,
      fin_to_inf_uvalue uv1 = fin_to_inf_uvalue uv2 ->
      uv1 = uv2.
  Proof.
    intros uv1 uv2 FININF.
    unfold fin_to_inf_uvalue in *.
    destruct (uvalue_convert_strict_safe uv1) as (?&?&?).
    destruct (uvalue_convert_strict_safe uv2) as (?&?&?).
    subst.
    rewrite e0 in e2. inv e2.
    auto.
  Qed.

  Lemma lift_SByte_injective :
    forall b1 b2,
      lift_SByte b1 = lift_SByte b2 ->
      b1 = b2.
  Proof.
    intros b1 b2 H.
    destruct b1, b2.
    cbn in *.
    inv H.
    apply fin_to_inf_uvalue_injective in H1, H3.
    subst.
    auto.
  Qed.


  Lemma inf_fin_read_byte_prop_MemPropT :
    forall addr_fin addr_inf ms_fin ms_inf byte_inf byte_fin,
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      sbyte_refine byte_inf byte_fin ->
      MemoryBigIntptr.MMEP.MMSP.read_byte_MemPropT addr_inf
        (MemoryBigIntptr.MMEP.MMSP.MemState_get_memory ms_inf)
        (ret (MemoryBigIntptr.MMEP.MMSP.MemState_get_memory ms_inf, byte_inf)) ->
      Memory64BitIntptr.MMEP.MMSP.read_byte_MemPropT addr_fin
        (Memory64BitIntptr.MMEP.MMSP.MemState_get_memory ms_fin)
        (ret (Memory64BitIntptr.MMEP.MMSP.MemState_get_memory ms_fin, byte_fin)).
  Proof.
intros addr_fin addr_inf ms_fin ms_inf byte_inf byte_fin MSR ADDR_CONV BYTE_REF RBP.
    (* TODO: make things opaque? *)
    destruct RBP as [ms_inf' [ms_inf'' [[MS MS'] READ]]].
    subst.
    destruct ms_inf eqn:MSINF. cbn in READ.
    destruct ms_fin eqn:MSFIN.

    break_match_hyp.
    (* read_byte_MemPropT may have UB... Which
                           means sbyte_refine byte_inf byte_fin might not
                           hold because byte_fin could be any byte.
     *)
    - assert (byte_inf = lift_SByte byte_fin) as BYTE'.
      { clear - BYTE_REF.
        red in BYTE_REF.
        erewrite lift_SByte_convert_SByte_inverse; eauto.
      }
      subst.

      destruct m.
      pose proof fin_inf_ptoi _ _ ADDR_CONV as PTOI.
      pose proof inf_fin_read_byte_raw MSR Heqo.
      destruct H as [byte_fin' [H BYTE_REF']].
      unfold Memory64BitIntptr.MMEP.MMSP.mem_state_memory in H.
      cbn in H.

      cbn.
      eexists. eexists.
      split; eauto.
      rewrite <- PTOI in H.
      rewrite H.
      erewrite inf_fin_access_allowed; cbn; eauto.
      break_match_goal; cbn; eauto.

      break_match_hyp.
      destruct READ; subst; auto.

      red in BYTE_REF'.
      cbn in H1.

      apply lift_SByte_convert_SByte_inverse in BYTE_REF'.
      rewrite <- H1 in BYTE_REF'.
      apply lift_SByte_injective in BYTE_REF'; subst; auto.

      cbn in Heqb0.
      rewrite Heqb0 in Heqb.
      discriminate.
    - epose proof inf_fin_read_byte_raw_None _ _ _ MSR Heqo.
      cbn.
      eexists. eexists.
      split; eauto.
      erewrite fin_inf_ptoi; eauto.
      destruct ms_memory_stack0; cbn in *.
      rewrite H.
      auto.
  Qed.


  (* Lemma inf_fin_read_byte_prop_MemPropT_exists : *)
  (*   forall addr_inf ms_fin ms_inf byte_inf, *)
  (*     MemState_refine ms_inf ms_fin -> *)
  (*     MemoryBigIntptr.MMEP.MMSP.read_byte_MemPropT addr_inf *)
  (*       (MemoryBigIntptr.MMEP.MMSP.MemState_get_memory ms_inf) *)
  (*       (ret (MemoryBigIntptr.MMEP.MMSP.MemState_get_memory ms_inf, byte_inf)) -> *)
  (*     exists addr_fin byte_fin, *)
  (*       Memory64BitIntptr.MMEP.MMSP.read_byte_MemPropT addr_fin *)
  (*         (Memory64BitIntptr.MMEP.MMSP.MemState_get_memory ms_fin) *)
  (*         (ret (Memory64BitIntptr.MMEP.MMSP.MemState_get_memory ms_fin, byte_fin)) /\ *)
  (*         InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin /\ *)
  (*         sbyte_refine byte_inf byte_fin. *)
  (* Proof. *)
  (*   intros addr_inf ms_fin ms_inf byte_inf MSR RBP. *)
  (*   (* TODO: make things opaque? *) *)
  (*   destruct RBP as [ms_inf' [ms_inf'' [[MS MS'] READ]]]. *)
  (*   subst. *)
  (*   destruct ms_inf eqn:MSINF. cbn in READ. *)
  (*   destruct ms_fin eqn:MSFIN. *)

  (*   break_match_hyp. *)
  (*   (* read_byte_MemPropT may have UB... Which *)
  (*                          means sbyte_refine byte_inf byte_fin might not *)
  (*                          hold because byte_fin could be any byte. *)
  (*    *) *)
  (*   - destruct m. *)
  (*     pose proof MemState_refine_convert_memory _ _ MSR as CONV_MEM. *)
  (*     pose proof inf_fin_read_byte_raw_exists CONV_MEM Heqo. *)
  (*     destruct H as [ptr_fin [byte_fin' [PTOI [H BYTE_REF]]]]. *)

  (*     unfold Memory64BitIntptr.MMEP.MMSP.mem_state_memory in H. *)
  (*     cbn in H. *)

  (*     cbn. *)
  (*     destruct addr_inf as [ptr_inf pr_inf]. *)
  (*     exfalso. *)
  (*     pose proof ITOP.int_to_ptr_ptr_to_int. *)
  (*     eapply H0. *)
  (*     cbn in *. *)
  (*     exists ( *)
  (*     exists ptr_fin. exists byte_fin'. *)
  (*     split; eauto. *)
  (*     2: { *)
  (*       split. *)
  (*       -  *)
  (*         cbn in *. *)
  (*         rewrite <- PTOI. *)
  (*     } *)
  (*     rewrite <- PTOI in H. *)
  (*     eexists. eexists. *)
  (*     split; auto. *)
  (*     rewrite H. *)
  (*     erewrite inf_fin_access_allowed; cbn; eauto. *)
  (*     break_match_goal; cbn; eauto. *)

  (*     break_match_hyp. *)
  (*     destruct READ; subst; auto. *)
  (*     unfold InfToFinAddrConvert.addr_convert; cbn. *)
  (*     unfold InfToFinAddrConvert.addr_convert; cbn. *)


  (*     red in BYTE_REF. *)
  (*     Set Nested Proofs Allowed. *)
  (*     (* TODO: Move this *) *)
  (*     Lemma lift_SByte_convert_SByte_inverse : *)
  (*       forall {b1 b2}, *)
  (*         convert_SByte b1 = NoOom b2 -> *)
  (*         lift_SByte b2 = b1. *)
  (*     Proof. *)
  (*     Admitted. *)

  (*     Lemma fin_to_inf_uvalue_injective : *)
  (*       forall uv1 uv2, *)
  (*         fin_to_inf_uvalue uv1 = fin_to_inf_uvalue uv2 -> *)
  (*         uv1 = uv2. *)
  (*     Proof. *)
  (*       intros uv1 uv2 FININF. *)
  (*       unfold fin_to_inf_uvalue in *. *)
  (*       destruct (uvalue_convert_strict_safe uv1) as (?&?&?). *)
  (*       destruct (uvalue_convert_strict_safe uv2) as (?&?&?). *)
  (*       subst. *)
  (*       rewrite e0 in e2. inv e2. *)
  (*       auto. *)
  (*     Qed. *)

  (*     Lemma lift_SByte_injective : *)
  (*       forall b1 b2, *)
  (*         lift_SByte b1 = lift_SByte b2 -> *)
  (*         b1 = b2. *)
  (*     Proof. *)
  (*       intros b1 b2 H. *)
  (*       destruct b1, b2. *)
  (*       cbn in *. *)
  (*       inv H. *)
  (*       apply fin_to_inf_uvalue_injective in H1, H3. *)
  (*       subst. *)
  (*       auto. *)
  (*     Qed. *)

  (*     apply lift_SByte_convert_SByte_inverse in BYTE_REF. *)
  (*     rewrite <- H1 in BYTE_REF. *)
  (*     apply lift_SByte_injective in BYTE_REF; subst; auto. *)

  (*     cbn in Heqb0. *)
  (*     rewrite Heqb0 in Heqb. *)
  (*     discriminate. *)
  (*   - epose proof inf_fin_read_byte_raw_None _ _ _ _ Heqo. *)
  (*     cbn. *)
  (*     eexists. eexists. *)
  (*     split; eauto. *)
  (*     erewrite fin_inf_ptoi; eauto. *)
  (*     rewrite H. *)
  (*     auto. *)

  (*     Unshelve. *)
  (*     all: clear READ. *)
  (*     + replace (Memory64BitIntptr.MMEP.MMSP.memory_stack_memory ms_memory_stack0) with (Memory64BitIntptr.MMEP.MMSP.memory_stack_memory *)
  (*                                                                                         (Memory64BitIntptr.MMEP.MMSP.MemState_get_memory ms_fin)). *)
  (*       replace (MemoryBigIntptr.MMEP.MMSP.memory_stack_memory ms_memory_stack) with (MemoryBigIntptr.MMEP.MMSP.memory_stack_memory *)
  (*                                                                                        (MemoryBigIntptr.MMEP.MMSP.MemState_get_memory ms_inf)). *)
  (*       eapply MemState_refine_convert_memory'; subst; eauto. *)
  (*       subst; cbn. auto. *)
  (*       subst; cbn. auto. *)
  (* Qed. *)

  Lemma fin_inf_read_byte_prop :
    forall {addr_fin addr_inf ms_fin ms_inf byte_inf byte_fin},
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      sbyte_refine byte_inf byte_fin ->
      Memory64BitIntptr.MMEP.MemSpec.read_byte_prop ms_fin addr_fin byte_fin ->
      MemoryBigIntptr.MMEP.MemSpec.read_byte_prop ms_inf addr_inf byte_inf.
  Proof.
    intros addr_fin addr_inf ms_fin ms_inf byte_inf byte_fin MSR ADDR_CONV BYTE_REF RBP.
    red. red in RBP.
    eapply fin_inf_read_byte_prop_MemPropT; eauto.
  Qed.

  Lemma inf_fin_read_byte_prop :
    forall {addr_fin addr_inf ms_fin ms_inf byte_inf byte_fin},
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      sbyte_refine byte_inf byte_fin ->
      MemoryBigIntptr.MMEP.MemSpec.read_byte_prop ms_inf addr_inf byte_inf ->
      Memory64BitIntptr.MMEP.MemSpec.read_byte_prop ms_fin addr_fin byte_fin.
  Proof.
    intros addr_fin addr_inf ms_fin ms_inf byte_fin MSR ADDR_CONV BYTE_REF RBP.
    red. red in RBP.
    eapply inf_fin_read_byte_prop_MemPropT; eauto.
  Qed.

  Lemma fin_inf_read_byte_spec :
    forall {addr_fin addr_inf ms_fin ms_inf byte_inf byte_fin},
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      sbyte_refine byte_inf byte_fin ->
      Memory64BitIntptr.MMEP.MemSpec.read_byte_spec ms_fin addr_fin byte_fin ->
      MemoryBigIntptr.MMEP.MemSpec.read_byte_spec ms_inf addr_inf byte_inf.
  Proof.
    intros addr_fin addr_inf ms_fin ms_inf byte_inf byte_fin MSR ADDR_CONV BYTE_REF READ_SPEC.
    destruct READ_SPEC.
    split.
    - eapply fin_inf_read_byte_allowed; eauto.
    - eapply fin_inf_read_byte_prop; eauto.
  Qed.

  Lemma fin_inf_read_byte_spec_exists :
    forall {addr_fin ms_fin ms_inf byte_fin},
      MemState_refine_prop ms_inf ms_fin ->
      Memory64BitIntptr.MMEP.MemSpec.read_byte_spec ms_fin addr_fin byte_fin ->
      exists addr_inf byte_inf,
        MemoryBigIntptr.MMEP.MemSpec.read_byte_spec ms_inf addr_inf byte_inf /\
          addr_refine addr_inf addr_fin /\
          sbyte_refine byte_inf byte_fin.
  Proof.
    intros addr_fin ms_fin ms_inf byte_fin MSR READ_SPEC.
    destruct READ_SPEC.
    exists (fin_to_inf_addr addr_fin).
    exists (lift_SByte byte_fin).

    pose proof (addr_convert_fin_to_inf_addr addr_fin).
    pose proof (sbyte_refine_lifted byte_fin).

    split; auto.

    split.
    - eapply fin_inf_read_byte_allowed; eauto.
    - eapply fin_inf_read_byte_prop; eauto.
  Qed.

  Lemma fin_inf_read_byte_spec_MemPropT' :
    forall addr_fin addr_inf ms_fin ms_inf byte_inf byte_fin,
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      sbyte_refine byte_inf byte_fin ->
      Memory64BitIntptr.MMEP.MemSpec.read_byte_spec_MemPropT addr_fin ms_fin (success_unERR_UB_OOM (ms_fin, byte_fin)) ->
      MemoryBigIntptr.MMEP.MemSpec.read_byte_spec_MemPropT addr_inf ms_inf (success_unERR_UB_OOM (ms_inf, byte_inf)).
  Proof.
    intros addr_fin addr_inf ms_fin ms_inf byte_inf byte_fin MSR ADDR_CONV BYTE_REF READ_SPEC.
    red. cbn.
    split; auto.
    red in READ_SPEC. cbn in READ_SPEC.
    destruct READ_SPEC.
    eapply fin_inf_read_byte_spec; eauto.
  Qed.

  (* Better form for MemPropT_fin_inf_bind *)
  Lemma fin_inf_read_byte_spec_MemPropT :
    forall {addr_fin addr_inf ms_fin ms_fin' ms_inf byte_fin},
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      Memory64BitIntptr.MMEP.MemSpec.read_byte_spec_MemPropT addr_fin ms_fin (success_unERR_UB_OOM (ms_fin', byte_fin)) ->
      exists byte_inf ms_inf',
        MemoryBigIntptr.MMEP.MemSpec.read_byte_spec_MemPropT addr_inf ms_inf (success_unERR_UB_OOM (ms_inf', byte_inf)) /\
          sbyte_refine byte_inf byte_fin /\
          MemState_refine_prop ms_inf' ms_fin'.
  Proof.
    intros addr_fin addr_inf ms_fin ms_fin' ms_inf byte_fin MSR ADDR_CONV READ_SPEC.

    repeat red in READ_SPEC.
    destruct READ_SPEC; subst.

    epose proof fin_inf_read_byte_spec MSR ADDR_CONV _ H0.
    do 2 eexists; split.
    repeat red.
    split; eauto.
    split; auto.
    apply sbyte_refine_lifted.

    Unshelve.
    apply sbyte_refine_lifted.
  Qed.

  Lemma fin_inf_read_bytes_spec' :
    forall a_fin a_inf n ms_fin ms_inf bytes_inf bytes_fin,
      InfToFinAddrConvert.addr_convert a_inf = NoOom a_fin ->
      MemState_refine_prop ms_inf ms_fin ->
      sbytes_refine bytes_inf bytes_fin ->
      Memory64BitIntptr.MMEP.MemSpec.read_bytes_spec a_fin n ms_fin (success_unERR_UB_OOM (ms_fin, bytes_fin)) ->
      MemoryBigIntptr.MMEP.MemSpec.read_bytes_spec a_inf n ms_inf (success_unERR_UB_OOM (ms_inf, bytes_inf)).
  Proof.
    intros a_fin a_inf n ms_fin ms_inf bytes_inf bytes_fin ADDR_CONV MEM_REF BYTES_REF READ_SPEC.

    (* TODO: Make these opaque earlier *)
    Opaque Memory64BitIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs.
    Opaque MemoryBigIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs.
    red. red in READ_SPEC.
    cbn in *.
    destruct READ_SPEC as (ms_fin' & addrs_fin & CONSEC & READ_SPEC).
    exists ms_inf.
    pose proof fin_inf_get_consecutive_ptrs_success_exists' a_fin a_inf n ms_fin ms_fin' addrs_fin ms_inf ADDR_CONV CONSEC as (addrs_inf & GCP & ADDRS_CONV).
    exists addrs_inf.
    split; auto.

    (* Not sure if induction is the right thing to do here *)
    generalize dependent a_fin.
    generalize dependent a_inf.
    generalize dependent n.
    generalize dependent bytes_fin.
    generalize dependent bytes_inf.
    induction ADDRS_CONV; intros bytes_inf bytes_fin BYTES_REF READ_SPEC n a_inf GCP a_fin ADDR_CONV CONSEC.
    - cbn in *.
      destruct READ_SPEC; subst; cbn.
      inv BYTES_REF.
      auto.
    - rewrite map_monad_unfold.
      cbn.

      rename l into addrs_fin.
      rename l' into addrs_inf.
      rename y into x_inf.
      rename x into x_fin.

      cbn in READ_SPEC.
      destruct READ_SPEC as [ms_fin'' [a [[MS READ_SPEC] READ_SPEC_REST]]]; subst.

      assert (ms_fin'' = ms_fin) as MSFIN.
      {
        (* TODO: make this a lemma *)
        Transparent Memory64BitIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs.
        unfold Memory64BitIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs in CONSEC.
        cbn in CONSEC.
        destruct CONSEC as [sab [ips [SEQ CONSEC]]].
        red in SEQ.
        break_match_hyp; inv SEQ.
        destruct CONSEC as [sab [addrs [CONSEC SEQ]]].
        red in CONSEC.
        break_match_hyp; inv CONSEC.
        red in SEQ.
        break_match_hyp; inv SEQ.                                                   auto.
        Opaque Memory64BitIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs.
      }
      subst.

      pose proof READ_SPEC_REST as READ_SPEC_REST'.
      destruct READ_SPEC_REST as [ms_fin' [bytes_fin' READ_SPEC_REST]].
      destruct READ_SPEC_REST as [READ_SPEC_REST [MS BYTES_FIN]].
      subst.

      exists ms_inf. exists (lift_SByte a).
      split.
      { split; auto.
        eapply fin_inf_read_byte_spec; eauto.
        apply sbyte_refine_lifted.
      }

      assert ((exists (pre : MemoryBigIntptr.MMEP.MMSP.MemState) (post : MemoryBigIntptr.MMEP.MMSP.MemState),
                  Within.within (InfLLVM.MEM.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs a_inf n) pre
                    (ret (x_inf :: addrs_inf)) post)).
      { exists ms_inf. exists ms_inf.
        cbn. red. cbn.
        auto.
      }

      inv BYTES_REF.
      rename H4 into BYTE_REF.
      rename H5 into BYTES_REF.
      specialize (IHADDRS_CONV _ _ BYTES_REF READ_SPEC_REST).

      epose proof InfLLVM.MEM.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs_cons _ _ _ _ H0.
      destruct H1 as [XA [[PTRS N] | [ptr' [ip' [len' [LEN [IP [GEP [pre [post WITHIN]]]]]]]]]].
      { subst.
        cbn in *.
        exists ms_inf. exists [].
        split; auto.
        split; auto.

        specialize (IHADDRS_CONV 0%nat a_inf).
        forward IHADDRS_CONV.
        { cbn.
          (* TODO: This should probably be a lemma *)
          Transparent MemoryBigIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs.
          unfold MemoryBigIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs.
          Opaque MemoryBigIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs.
          cbn.
          exists ms_inf. exists [].
          split; auto.
          exists ms_inf. exists [].
          cbn.
          auto.
        }

        specialize (IHADDRS_CONV _ H).
        inv ADDRS_CONV.
        forward IHADDRS_CONV.
        { cbn.
          (* TODO: This should probably be a lemma *)
          Transparent Memory64BitIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs.
          unfold Memory64BitIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs.
          Opaque Memory64BitIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs.
          cbn.
          exists ms_fin'. exists [].
          split; auto.
          exists ms_fin'. exists [].
          cbn.
          auto.
        }

        destruct IHADDRS_CONV; subst.
        red in BYTE_REF.
        erewrite lift_SByte_convert_SByte_inverse; eauto.
      }

      pose proof H0 as WITHIN_INF.
      destruct H0 as [pre' [post' WITHIN']].
      cbn in WITHIN'.
      red in WITHIN'.
      cbn in WITHIN'.


      subst.
      cbn in WITHIN.
      red in WITHIN.
      cbn in WITHIN.

      pose proof WITHIN as PREPOST.
      eapply MemoryBigIntptr.MMEP.get_consecutive_ptrs_MemPropT_MemState_eq in PREPOST.
      subst.

      rename l into bytes_inf'.
      exists ms_inf. exists bytes_inf'.
      split; auto.

      destruct addrs_inf as [? | a_inf' addrs_inf].
      {
        destruct addrs_fin as [? | a_fin' addrs_fin].
        {
          cbn in READ_SPEC_REST.
          destruct READ_SPEC_REST; subst.
          inv BYTES_REF.
          cbn; auto.
        }

        (* Should be a contradiction *)
        inv ADDRS_CONV.
      }

      destruct addrs_fin as [? | a_fin' addrs_fin].
      { (* Should be a contradiction *)
        inv ADDRS_CONV.
      }

      eapply IHADDRS_CONV.
      + eapply MemoryBigIntptr.MMEP.get_consecutive_ptrs_MemPropT_MemState.
        eapply WITHIN.
      + (* How do I know ptr' is safe to convert
                               to a finite pointer?

                               I know it's a_inf + 1...

                               Need to show that a_inf' is a_inf + 1
                               as well, and that it relates to a_fin'.
         *)

        (* ptr' is a_inf + 1 (AKA a_inf'). It
                               should share the same provenance as well.
         *)

        pose proof (MemoryBigIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs_nth_eq1  a_inf (S len') (a_inf :: a_inf' :: addrs_inf) (M:=(MemPropT MemoryBigIntptr.MMEP.MMSP.MemState))).
        forward H0.
        { red. red.
          intros ms x0.
          split.
          - intros GCP'.
            cbn.
            (* Ideally want to use GCP to show this... *)
            assert (exists (pre : MemoryBigIntptr.MMEP.MMSP.MemState) (post : MemoryBigIntptr.MMEP.MMSP.MemState),
                       @Within.within (MemPropT MemoryBigIntptr.MMEP.MMSP.MemState) (@MemPropT_Eq1 MemoryBigIntptr.MMEP.MMSP.MemState) err_ub_oom MemoryBigIntptr.MMEP.MMSP.MemState MemoryBigIntptr.MMEP.MMSP.MemState _ _ (MemoryBigIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs a_inf (S len')) pre (fmap snd x0) post).
            { exists ms. exists ms.
              red. red. red.
              destruct_err_ub_oom x0;
                cbn; auto.

              destruct x1; cbn in *.
              pose proof GCP' as GCP''.
              assert (success_unERR_UB_OOM (m, l) = @ret _ _ _ (m, l)); cbn; auto.
              rewrite H1 in GCP''.

              pose proof MemoryBigIntptr.MMEP.get_consecutive_ptrs_MemPropT_MemState_eq a_inf (S len') l ms m GCP''; subst.
              eauto.
            }

            pose proof MemoryBigIntptr.CP.CONCBASE.MemHelpers.get_consecutive_ptrs_success_always_succeeds (M:=(MemPropT MemoryBigIntptr.MMEP.MMSP.MemState)) (B:=err_ub_oom) a_inf (S len') (a_inf :: a_inf' :: addrs_inf) _ WITHIN_INF H1.
            destruct_err_ub_oom x0; cbn in *; inv H2.
            destruct x1; cbn in *; subst.
            pose proof GCP' as MM.
            apply MemoryBigIntptr.MMEP.get_consecutive_ptrs_MemPropT_MemState_eq in MM.
            subst.
            split; auto.
          - intros H1.
            cbn in H1.
            destruct_err_ub_oom x0; try inv H1.
            destruct x1.
            destruct H1.
            subst.
            pose proof WITHIN'.
            apply MemoryBigIntptr.MMEP.get_consecutive_ptrs_MemPropT_MemState_eq in H1; subst.
            eapply MemoryBigIntptr.MMEP.get_consecutive_ptrs_MemPropT_MemState.
            eapply WITHIN'.
        }

        specialize (H0 a_inf' 1%nat).
        forward H0; cbn; auto.
        destruct H0 as [ix [IX GEP_IX]].

        (* Show that ip' = ix *)
        assert (ip' = ix) as IPIX.
        {
          cbn in IX.
          inv IX.
          unfold InterpreterStackBigIntptr.LP.IP.to_Z in IP.
          auto.
        }
        subst.

        rewrite GEP in GEP_IX.
        inv GEP_IX.
        inv ADDRS_CONV.
        eauto.
      + (* Should follow from CONSEC *)

        assert ((exists (pre : FinMem.MMEP.MMSP.MemState) (post : FinMem.MMEP.MMSP.MemState),
                    Within.within (FinLLVM.MEM.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs a_fin (S len')) pre
                      (ret (x_fin :: a_fin' :: addrs_fin)) post)).
        {
          exists ms_fin'. exists ms_fin'.
          cbn. red. cbn.
          auto.
        }

        pose proof FinMem.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs_cons _ _ _ _ H0.
        destruct H1.
        destruct H2.
        { destruct H2; discriminate.
        }

        destruct H2 as [ptr'' [ip [len'' [LEN [IP' [GEP'' WITHIN'']]]]]].
        (* GEP'' suggests ptr'' = a_fin' *)
        assert (ptr'' = a_fin').
        {
          subst.
          pose proof FinMem.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs_cons _ _ _ _ WITHIN''.
          destruct H1.
          auto.
        }
        subst.

        destruct WITHIN'' as [pre [post'' WITHIN'']].
        cbn in WITHIN''.
        red in WITHIN''.
        cbn in WITHIN''.
        pose proof WITHIN''.
        inv LEN.
        apply FinMem.MMEP.get_consecutive_ptrs_MemPropT_MemState_eq in H1; subst.
        eapply FinMem.MMEP.get_consecutive_ptrs_MemPropT_MemState; eauto.
        eapply WITHIN''.
      + split; auto.
        red in BYTE_REF.
        erewrite lift_SByte_convert_SByte_inverse; eauto.
  Qed.

  (* Form that's better suited to MemPropT_fin_inf_bind *)
  Lemma fin_inf_read_bytes_spec :
    forall a_fin a_inf n ms_fin ms_fin' ms_inf bytes_fin,
      InfToFinAddrConvert.addr_convert a_inf = NoOom a_fin ->
      MemState_refine_prop ms_inf ms_fin ->
      Memory64BitIntptr.MMEP.MemSpec.read_bytes_spec a_fin n ms_fin (success_unERR_UB_OOM (ms_fin', bytes_fin)) ->
      exists bytes_inf ms_inf',
        MemoryBigIntptr.MMEP.MemSpec.read_bytes_spec a_inf n ms_inf (success_unERR_UB_OOM (ms_inf', bytes_inf)) /\
          sbytes_refine bytes_inf bytes_fin /\
          MemState_refine_prop ms_inf' ms_fin'.
  Proof.
    intros a_fin a_inf n ms_fin ms_fin' ms_inf bytes_fin ADDR_CONV MEM_REF READ_SPEC.

    eapply MemPropT_fin_inf_bind.
    4: apply READ_SPEC.
    all: eauto.

    { intros a_fin0 ms_fin_ma GCP.
      eapply fin_inf_get_consecutive_ptrs_success_exists; eauto.
      eapply GCP.
    }

    intros ms_inf0 ms_fin0 ms_fin'0 a_fin0 a_inf0 b_fin ADDRS MSR READ.

    eapply MemPropT_fin_inf_map_monad.
    4: apply READ.
    all: eauto.
    2: {
      apply Forall2_flip in ADDRS.
      cbn in ADDRS.
      apply ADDRS.
    }

    intros a_fin1 a_inf1 b_fin0 ms_fin1 ms_inf1 ms_fin_ma MSR' CONV RBS.
    eapply fin_inf_read_byte_spec_MemPropT; eauto.
    apply CONV.
  Qed.

  Lemma fin_inf_disjoint_ptr_byte :
    forall addr_fin addr_fin' addr_inf addr_inf',
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      InfToFinAddrConvert.addr_convert addr_inf' = NoOom addr_fin' ->
      Memory64BitIntptr.MMEP.MemSpec.disjoint_ptr_byte addr_fin addr_fin' <->
        MemoryBigIntptr.MMEP.MemSpec.disjoint_ptr_byte addr_inf addr_inf'.
  Proof.
    intros addr_fin addr_fin' addr_inf addr_inf' CONV CONV'.
    split; intros DISJOINT.
    - red in DISJOINT.
      red.
      unfold InfToFinAddrConvert.addr_convert in *.
      destruct addr_inf, addr_inf'.
      cbn in *.
      erewrite FinLP.ITOP.ptr_to_int_int_to_ptr in DISJOINT; [| apply CONV].
      erewrite FinLP.ITOP.ptr_to_int_int_to_ptr in DISJOINT; [| apply CONV'].
      auto.
    - red in DISJOINT.
      red.
      unfold InfToFinAddrConvert.addr_convert in *.
      destruct addr_inf, addr_inf'.
      cbn in *.
      erewrite FinLP.ITOP.ptr_to_int_int_to_ptr; [| apply CONV].
      erewrite FinLP.ITOP.ptr_to_int_int_to_ptr; [| apply CONV'].
      auto.
  Qed.

  (* TODO: Move this into lemmas about primitives *)
  Lemma fin_byte_allocated_read_byte_raw :
    forall ms ptr aid,
      Memory64BitIntptr.MMEP.MemSpec.byte_allocated ms ptr aid ->
      exists byte,
        Memory64BitIntptr.MMEP.MMSP.read_byte_raw
          (Memory64BitIntptr.MMEP.MMSP.memory_stack_memory
             (Memory64BitIntptr.MMEP.MMSP.MemState_get_memory ms))
          (LLVMParams64BitIntptr.PTOI.ptr_to_int ptr) = Some (byte, aid).
  Proof.
    intros ms ptr aid ALLOC.
    cbn in ALLOC.
    destruct ALLOC as [ms' [b ALLOC]].
    destruct ALLOC as (?&?&?).
    subst.
    red in H.
    destruct H.
    clear H0.
    Transparent Memory64BitIntptr.MMEP.MMSP.addr_allocated_prop.
    unfold Memory64BitIntptr.MMEP.MMSP.addr_allocated_prop in H.
    cbn in H.

    destruct H as [ms' [ms'' [[MS MS'] H]]].
    break_match_hyp.
    {
      destruct m.
      exists s.
      destruct H.
      cbn in H0.
      destruct (LLVMParams64BitIntptr.PROV.aid_eq_dec aid a) eqn:AID;
        cbn in *; subst; try discriminate.
      auto.
    }

    {
      destruct H; discriminate.
    }
  Qed.

  (* TODO: Move this into lemmas about primitives *)
  Lemma inf_byte_allocated_read_byte_raw :
    forall ms ptr aid,
      MemoryBigIntptr.MMEP.MemSpec.byte_allocated ms ptr aid ->
      exists byte,
        MemoryBigIntptr.MMEP.MMSP.read_byte_raw
          (MemoryBigIntptr.MMEP.MMSP.memory_stack_memory
             (MemoryBigIntptr.MMEP.MMSP.MemState_get_memory ms))
          (LLVMParamsBigIntptr.PTOI.ptr_to_int ptr) = Some (byte, aid).
  Proof.
    intros ms ptr aid ALLOC.
    cbn in ALLOC.
    destruct ALLOC as [ms' [b ALLOC]].
    destruct ALLOC as (?&?&?).
    subst.
    red in H.
    destruct H.
    clear H0.
    Transparent MemoryBigIntptr.MMEP.MMSP.addr_allocated_prop.
    unfold MemoryBigIntptr.MMEP.MMSP.addr_allocated_prop in H.
    cbn in H.

    destruct H as [ms' [ms'' [[MS MS'] H]]].
    break_match_hyp.
    {
      destruct m.
      exists s.
      destruct H.
      cbn in H0.
      destruct (LLVMParamsBigIntptr.PROV.aid_eq_dec aid a) eqn:AID;
        cbn in *; subst; try discriminate.
      auto.
    }

    {
      destruct H; discriminate.
    }
  Qed.

  Lemma read_byte_spec_ref_byte_is_lifted :
    forall ms_inf ms_fin addr_inf addr_fin byte_inf byte_fin,
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      Memory64BitIntptr.MMEP.MemSpec.read_byte_spec ms_fin addr_fin byte_fin ->
      MemoryBigIntptr.MMEP.MemSpec.read_byte_spec ms_inf addr_inf byte_inf ->
      byte_inf = lift_SByte byte_fin.
  Proof.
    intros ms_inf ms_fin addr_inf addr_fin byte_inf byte_fin MEM_REF ADDR_CONV READ_FIN READ_INF.
    destruct READ_FIN, READ_INF.
    cbn in read_byte_value, read_byte_value0.
    destruct read_byte_value as [ms_fin' [ms_fin'' [[MS_FIN MS_FIN'] READ_FIN]]].
    destruct read_byte_value0 as [ms_inf' [ms_inf'' [[MS_INF MS_INF'] READ_INF]]].
    move READ_FIN after READ_INF.
    subst.
    break_match_hyp; rewrite memory_stack_memory_mem_state_memory_fin in Heqo.
    {
      pose proof Heqo as Heqo'.
      destruct m.
      epose proof fin_inf_read_byte_raw MEM_REF Heqo as READ_INF_RAW.
      assert (LLVMParams64BitIntptr.PTOI.ptr_to_int addr_fin = LLVMParamsBigIntptr.PTOI.ptr_to_int addr_inf).
      {
        destruct addr_inf.
        cbn in ADDR_CONV.
        erewrite FinLP.ITOP.ptr_to_int_int_to_ptr; eauto.
      }
      rewrite H in READ_INF_RAW.
      rewrite memory_stack_memory_mem_state_memory, READ_INF_RAW in READ_INF.

      (* READ_FIN and READ_INF both have an access control check...
                                     Presumably this check should be true for both or false for both...
       *)

      (* If access is not allowed, then
                                    READ_FIN and READ_INF are both
                                    useless True propositions.

                                    mem_byte_value and mem_byte_aid
                                    come from the read_byte_raw
                                    operation... They're from the
                                    mem_byte that is read from memory.

                                     LLVMParamsBigIntptr.PROV.access_allowed
                                       (LLVMParamsBigIntptr.PROV.address_provenance
                                       addr_inf) (snd (lift_SByte mem_byte_value,
                                       mem_byte_aid)) = false

                                    It means that read_byte_spec is a
                                    contradiction, presumably in
                                    read_byte_allowed_spec...

                                    read_byte_allowed states:

                                    Memory64BitIntptr.MMEP.MemSpec.read_byte_allowed =
                                      fun (ms : Memory64BitIntptr.MMEP.MMSP.MemState) (ptr : LLVMParams64BitIntptr.ADDR.addr) =>
                                      exists aid : LLVMParams64BitIntptr.PROV.AllocationId,
                                      Memory64BitIntptr.MMEP.MemSpec.byte_allocated ms ptr aid /\
                                      LLVMParams64BitIntptr.PROV.access_allowed (LLVMParams64BitIntptr.PROV.address_provenance ptr) aid = true

                                   I.e., there is some mem_byte in
                                   memory at 'ptr' with the allocation
                                   id 'aid', and the provenance of our
                                   pointer is allowed to access it.

       *)
      destruct read_byte_allowed_spec as [aid_fin [BYTE_ALLOCATED_FIN ACCESS_ALLOWED_FIN]].
      destruct read_byte_allowed_spec0 as [aid_inf [BYTE_ALLOCATED_INF ACCESS_ALLOWED_INF]].

      (* With byte_allocated... Maybe I
                                     can conclude that aid_fin = aid_inf
                                     = mem_byte_aid

                                     Yep... It uses read_byte_raw
                                     behind the scenes.

                                     Use below lemmas and Heqo + Heqo'
       *)

      apply fin_byte_allocated_read_byte_raw in BYTE_ALLOCATED_FIN as [byte_fin' BYTE_ALLOCATED_FIN].
      apply inf_byte_allocated_read_byte_raw in BYTE_ALLOCATED_INF as [byte_inf' BYTE_ALLOCATED_INF].

      rewrite memory_stack_memory_mem_state_memory_fin in BYTE_ALLOCATED_FIN.
      rewrite memory_stack_memory_mem_state_memory in BYTE_ALLOCATED_INF.
      rewrite BYTE_ALLOCATED_FIN in Heqo.
      rewrite BYTE_ALLOCATED_INF in READ_INF_RAW.
      inv Heqo; inv READ_INF_RAW.

      cbn in *.
      rewrite ACCESS_ALLOWED_INF in READ_INF.
      rewrite ACCESS_ALLOWED_FIN in READ_FIN.

      destruct READ_INF.
      destruct READ_FIN.
      subst.
      auto.
    }

    { (* Read failed, Heqo *)
      (* Probably a contradiction with read_byte_allowed_spec *)
      clear READ_INF.
      destruct read_byte_allowed_spec as [aid_fin [BYTE_ALLOCATED_FIN ACCESS_ALLOWED_FIN]].
      apply fin_byte_allocated_read_byte_raw in BYTE_ALLOCATED_FIN.
      destruct BYTE_ALLOCATED_FIN.
      rewrite memory_stack_memory_mem_state_memory_fin in H.
      rewrite H in Heqo.
      inv Heqo.
    }
  Qed.

  (* TODO: Move this *)
  Lemma read_byte_allowed_read_byte_raw :
    forall {ms ptr},
      MemoryBigIntptr.MMEP.MemSpec.read_byte_allowed ms ptr ->
      exists byte aid,
        MemoryBigIntptr.MMEP.MMSP.read_byte_raw (InfMem.MMEP.MMSP.mem_state_memory ms) (LLVMParamsBigIntptr.PTOI.ptr_to_int ptr) = Some (byte, aid) /\
          InfPROV.access_allowed (InfLP.PROV.address_provenance ptr) aid = true.
  Proof.
    intros ms ptr ALLOWED.
    red in ALLOWED.
    destruct ALLOWED as [aid [BYTE_ALLOCATED ALLOWED]].
    repeat red in BYTE_ALLOCATED.
    destruct BYTE_ALLOCATED as [ms' [a [ADDR_ALLOCATED [MS A]]]]; subst.
    red in ADDR_ALLOCATED.
    destruct ADDR_ALLOCATED as [ADDR_ALLOCATED PROV].
    repeat red in ADDR_ALLOCATED.
    destruct ADDR_ALLOCATED as [ms' [ms'' [GET_MEM_STATE READ]]].
    cbn in GET_MEM_STATE. destruct GET_MEM_STATE; subst.
    break_match_hyp.
    2: {
      cbn in READ.
      destruct READ; discriminate.
    }

    destruct m.
    exists s. exists a.
    split; auto.

    cbn in READ.
    destruct READ as [_ AID].
    destruct (LLVMParamsBigIntptr.PROV.aid_eq_dec aid a) eqn:AID'; subst; cbn in *; try discriminate.
    auto.
  Qed.

  (* TODO: Move and make something for both fin / inf memory *)
  Lemma read_byte_spec_read_byte_raw :
    forall {ms ptr byte},
      MemoryBigIntptr.MMEP.MemSpec.read_byte_spec ms ptr byte ->
      exists aid,
        MemoryBigIntptr.MMEP.MMSP.read_byte_raw (InfMem.MMEP.MMSP.mem_state_memory ms) (LLVMParamsBigIntptr.PTOI.ptr_to_int ptr) = Some (byte, aid) /\
          InfPROV.access_allowed (InfLP.PROV.address_provenance ptr) aid = true.
  Proof.
    intros ms ptr byte [ALLOWED READ].
    apply read_byte_allowed_read_byte_raw in ALLOWED as [byte' [aid [READ' ALLOWED]]].
    exists aid. split; auto.
    cbn in READ.
    destruct READ as [ms' [ms'' [[MS MS'] READ]]]; subst.
    destruct ms.
    destruct ms_memory_stack.
    cbn in READ, READ'.
    rewrite READ' in READ.
    cbn in READ.
    rewrite ALLOWED in READ.
    destruct READ; subst.
    auto.
  Qed.

  Lemma inf_fin_read_byte_spec :
    forall {ms_inf ms_fin ptr_inf ptr_fin byte_inf},
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert ptr_inf = NoOom ptr_fin ->
      MemoryBigIntptr.MMEP.MemSpec.read_byte_spec ms_inf ptr_inf byte_inf ->
      exists byte_fin,
        Memory64BitIntptr.MMEP.MemSpec.read_byte_spec ms_fin ptr_fin byte_fin /\
          sbyte_refine byte_inf byte_fin.
  Proof.
    intros ms_inf ms_fin ptr_inf ptr_fin byte_inf MEM_REF ADDR_CONV RBS.
    pose proof read_byte_spec_read_byte_raw RBS as [aid [READ_RAW_INF ALLOWED]].

    cbn in READ_RAW_INF.

    assert (LLVMParams64BitIntptr.PTOI.ptr_to_int ptr_fin = LLVMParamsBigIntptr.PTOI.ptr_to_int ptr_inf) as PTR.
    { eapply fin_inf_ptoi; eauto.
    }

    epose proof inf_fin_read_byte_raw MEM_REF READ_RAW_INF as [byte_fin [READ_BYTE_RAW_FIN BYTE_REF]].

    exists byte_fin.
    split.
    { (* Read byte spec *)
      split.
      - red.
        exists aid.
        split.
        + cbn. eexists. exists true.
          split; auto.
          cbn.
          red.
          split.
          2: {
            intros ms' x H.
            cbn in *.
            inv H.
            cbn.
            auto.
          }

          cbn.
          exists (Memory64BitIntptr.MMEP.MMSP.MemState_get_memory ms_fin).
          exists (Memory64BitIntptr.MMEP.MMSP.MemState_get_memory ms_fin).
          split; auto.

          rewrite PTR.
          rewrite memory_stack_memory_mem_state_memory_fin.
          rewrite READ_BYTE_RAW_FIN.
          split; auto.
          apply LLVMParams64BitIntptr.PROV.aid_eq_dec_refl.
        + eapply inf_fin_access_allowed; eauto.
      - repeat red.
        do 2 eexists.
        split; [split; auto|].
        cbn.

        rewrite PTR.
        rewrite memory_stack_memory_mem_state_memory_fin.
        rewrite READ_BYTE_RAW_FIN.
        cbn.
        erewrite inf_fin_access_allowed; eauto; cbn.
        split; auto.
    }

    { (* Byte refinement *)
      auto.
    }
  Qed.

  (* TODO: Move this *)
  Lemma inf_fin_read_byte_prop_exists :
    forall {ptr_inf byte_inf ms_inf ms_fin},
      MemState_refine_prop ms_inf ms_fin ->
      InfMem.MMEP.MemSpec.read_byte_prop ms_inf ptr_inf byte_inf ->
      exists ptr_fin byte_fin,
        FinMem.MMEP.MemSpec.read_byte_prop ms_fin ptr_fin byte_fin /\
          addr_refine ptr_inf ptr_fin /\
          sbyte_refine byte_inf byte_fin.
  Proof.
    intros ptr_inf byte_inf ms_inf ms_fin MSR RBP.
  Admitted.

  Lemma inf_fin_read_byte_spec_exists :
    forall {ms_inf ms_fin ptr_inf byte_inf},
      MemState_refine_prop ms_inf ms_fin ->
      MemoryBigIntptr.MMEP.MemSpec.read_byte_spec ms_inf ptr_inf byte_inf ->
      exists ptr_fin byte_fin,
        Memory64BitIntptr.MMEP.MemSpec.read_byte_spec ms_fin ptr_fin byte_fin /\
          sbyte_refine byte_inf byte_fin /\
          addr_refine ptr_inf ptr_fin.
  Proof.
    intros ms_inf ms_fin ptr_inf byte_inf MEM_REF RBS.
    pose proof read_byte_spec_read_byte_raw RBS as [aid [READ_RAW_INF ALLOWED]].

    cbn in READ_RAW_INF.

    pose proof RBS.
    destruct H.
    epose proof inf_fin_read_byte_prop_exists MEM_REF read_byte_value as (ptr_fin&byte_fin&RBP_FIN&ADDR_REF&BYTE_REF).
    exists ptr_fin. exists byte_fin.
    split; auto.

    epose proof inf_fin_read_byte_raw MEM_REF READ_RAW_INF as [byte_fin' [READ_BYTE_RAW_FIN BYTE_REF']].

    assert (LLVMParams64BitIntptr.PTOI.ptr_to_int ptr_fin = LLVMParamsBigIntptr.PTOI.ptr_to_int ptr_inf) as PTR.
    { eapply fin_inf_ptoi; eauto.
    }

    { (* Read byte spec *)
      split.
      - red.
        exists aid.
        split.
        + cbn. eexists. exists true.
          split; auto.
          cbn.
          red.
          split.
          2: {
            intros ms' x H.
            cbn in *.
            inv H.
            cbn.
            auto.
          }

          cbn.
          exists (Memory64BitIntptr.MMEP.MMSP.MemState_get_memory ms_fin).
          exists (Memory64BitIntptr.MMEP.MMSP.MemState_get_memory ms_fin).
          split; auto.

          rewrite PTR.
          rewrite memory_stack_memory_mem_state_memory_fin.
          rewrite READ_BYTE_RAW_FIN.
          split; auto.
          apply LLVMParams64BitIntptr.PROV.aid_eq_dec_refl.
        + eapply inf_fin_access_allowed; eauto.
      - repeat red.
        do 2 eexists.
        split; [split; auto|].
        cbn.

        rewrite PTR.
        rewrite memory_stack_memory_mem_state_memory_fin.
        rewrite READ_BYTE_RAW_FIN.
        cbn.
        erewrite inf_fin_access_allowed; eauto; cbn.
        split; auto.

        unfold sbyte_refine in *.
        rewrite BYTE_REF in BYTE_REF'.
        inv BYTE_REF'; auto.
    }
  Qed.

  (* TODO: Move this *)
  (* TODO: Ask about in meeting? *)
  (* TODO: This may not currently be true
     because of how lift_memory works...

     No constraint on the bounds of addresses... This can be changed,
     though... May make sense to just add it as another condition to
     MemState_refine_prop.
   *)
  Lemma fin_inf_big_addresses_no_byte_to_read :
    forall ms_inf ms_fin addr_inf oom_msg,
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert addr_inf = Oom oom_msg ->
      MemoryBigIntptr.MMEP.MMSP.read_byte_raw (InfMem.MMEP.MMSP.mem_state_memory ms_inf) (LLVMParamsBigIntptr.PTOI.ptr_to_int addr_inf) = None.
  Proof.
    intros mem_inf mem_fin addr_inf oom_msg MEM_CONV ADDR_CONV.
    unfold InfToFinAddrConvert.addr_convert in *.
    destruct addr_inf as [ix_inf pr].
  Admitted.

  (* TODO: a little unsure of this one, but it seems plausible. *)
  Lemma fin_to_inf_dvalue_refine_strict' :
    forall d_inf d_fin,
      DVC1.dvalue_refine_strict d_inf d_fin ->
      d_inf = fin_to_inf_dvalue d_fin.
  Proof.
    intros d_inf d_fin H.
    rewrite DVC1.dvalue_refine_strict_equation in H.
    unfold fin_to_inf_dvalue.
    break_match; cbn in *.
    destruct p.
    clear Heqs.

    induction d_inf;
      try solve
        [ rewrite DVC1.dvalue_convert_strict_equation in H;
          cbn in *; inv H;
          rewrite DVC2.dvalue_convert_strict_equation in e;
          cbn in *; inv e;
          auto
        ].
    - rewrite DVC1.dvalue_convert_strict_equation in H.
      cbn in *.
      break_match_hyp; inv H.
      rewrite DVC2.dvalue_convert_strict_equation in e.
      cbn in *.
      break_match_hyp; inv e.
      rewrite DVC1.dvalue_convert_strict_equation in e0.
      cbn in *.
      break_match_hyp; inv e0.

      pose proof InfToFinAddrConvert.addr_convert_injective a a1 a0 Heqo Heqo1.
      subst.
      auto.
    - rewrite DVC1.dvalue_convert_strict_equation in H.
      cbn in *; break_match_hyp; inv H.
      rewrite DVC2.dvalue_convert_strict_equation in e.
      cbn in *; inv e.
      rewrite DVC1.dvalue_convert_strict_equation in e0.
      cbn in *; break_match_hyp; inv e0.
      admit. (* Some painful IP / BigIP reasoning *)
    - rewrite DVC1.dvalue_convert_strict_equation in H.
      cbn in *; break_match_hyp; inv H.
      rewrite DVC2.dvalue_convert_strict_equation in e.
      cbn in *; break_match_hyp; inv e.
      rewrite DVC1.dvalue_convert_strict_equation in e0.
      cbn in *; break_match_hyp; inv e0.

      induction fields.
      + cbn in *. inv Heqo.
        cbn in *. inv Heqo0.
        reflexivity.
      + rewrite map_monad_InT_unfold in Heqo.
        cbn in *.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H1.

        rewrite map_monad_InT_unfold in Heqo0.
        cbn in *.
        break_match_hyp; inv Heqo0.
        break_match_hyp; inv H1.

        rewrite map_monad_InT_unfold in Heqo1.
        cbn in *.
        break_match_hyp; inv Heqo1.
        break_match_hyp; inv H1.
        admit.
    - admit.
    - admit.
    - admit.
  Admitted.

  (** Lemmas about writing bytes *)
  Lemma fin_inf_set_byte_memory :
    forall {addr_inf addr_fin byte_inf byte_fin ms_fin ms_fin' ms_inf},
      Heap_in_bounds ms_fin' ->
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      sbyte_refine byte_inf byte_fin ->
      Memory64BitIntptr.MMEP.MemSpec.set_byte_memory ms_fin addr_fin byte_fin ms_fin' ->
      exists ms_inf',
        MemoryBigIntptr.MMEP.MemSpec.set_byte_memory ms_inf addr_inf byte_inf ms_inf' /\
          MemState_refine_prop ms_inf' ms_fin'.
  Proof.
    intros addr_inf addr_fin byte_inf byte_fin ms_fin ms_fin' ms_inf HIB REF CONV BYTE_REF SET.

    pose proof (lift_MemState_refine_prop ms_fin' HIB) as REF'.
    exists (lift_MemState ms_fin').

    destruct SET.
    split.
    2: {
      apply lift_MemState_refine_prop. assumption.
    }

    split.
    - eapply fin_inf_read_byte_spec; eauto.
    - intros ptr' DISJOINT byte'.
      split; intros READ.
      + (* Old memory to new *)
        destruct (InfToFinAddrConvert.addr_convert ptr') eqn:CONVPTR.
        {
          (* ptr' exists in the finite space as 'a' *)
          pose proof fin_inf_disjoint_ptr_byte _ _ _ _ CONV CONVPTR as [_ DISJOINT_a].
          specialize (DISJOINT_a DISJOINT).
          specialize (old_lu a).

          (* a is disjoint from addr_fin, which means that old_lu should hold

                               If there's a byte to read in ms_fin
                               then the same byte can be read in
                               ms_fin'...

                               Then with H we can conclude...

                               MemoryBigIntptr.MMEP.MemSpec.read_byte_spec ms_inf' ptr' (lift_SByte ?byte_fin)

                               But I don't know how this relates to byte' in the goal.

           *)

          specialize (old_lu DISJOINT_a).

          pose proof inf_fin_read_byte_spec REF CONVPTR READ as [byte_fin' [READ_FIN BYTE_REF']].
          apply old_lu in READ_FIN.
          epose proof fin_inf_read_byte_spec REF' CONVPTR _ READ_FIN; eauto.
        }

        destruct READ.

        destruct read_byte_allowed_spec.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        red in H.
        destruct H.
        cbn in H1.
        cbn in H.
        Transparent MemoryBigIntptr.MMEP.MMSP.addr_allocated_prop.
        unfold MemoryBigIntptr.MMEP.MMSP.addr_allocated_prop in H.
        cbn in H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        subst.
        clear read_byte_value.
        rewrite memory_stack_memory_mem_state_memory in H3.
        erewrite fin_inf_big_addresses_no_byte_to_read in H3; eauto.
        destruct H3, H1.
        destruct ms_inf; cbn in *; subst.
        discriminate.
      + (* New memory to old *)
        destruct (InfToFinAddrConvert.addr_convert ptr') eqn:CONVPTR.
        {
          (* ptr' exists in the finite space as 'a' *)
          pose proof fin_inf_disjoint_ptr_byte _ _ _ _ CONV CONVPTR as [_ DISJOINT_a].
          specialize (DISJOINT_a DISJOINT).
          specialize (old_lu a).

          (* a is disjoint from addr_fin, which means that old_lu should hold

                               If there's a byte to read in ms_fin
                               then the same byte can be read in
                               ms_fin'...

                               Then with H we can conclude...

                               MemoryBigIntptr.MMEP.MemSpec.read_byte_spec ms_inf' ptr' (lift_SByte ?byte_fin)

                               But I don't know how this relates to byte' in the goal.
           *)

          specialize (old_lu DISJOINT_a).

          pose proof inf_fin_read_byte_spec REF' CONVPTR READ as [byte_fin' [READ_FIN BYTE_REF']].
          apply old_lu in READ_FIN.
          epose proof fin_inf_read_byte_spec REF CONVPTR _ READ_FIN; eauto.
        }

        destruct READ.

        destruct read_byte_allowed_spec.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        red in H.
        destruct H.
        cbn in H1.
        cbn in H.
        Transparent MemoryBigIntptr.MMEP.MMSP.addr_allocated_prop.
        unfold MemoryBigIntptr.MMEP.MMSP.addr_allocated_prop in H.
        cbn in H.
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        clear read_byte_value.
        subst.
        rewrite memory_stack_memory_mem_state_memory in H3.
        erewrite fin_inf_big_addresses_no_byte_to_read in H3; eauto.
        destruct H3, H1.
        destruct ms_inf; cbn in *; subst.
        discriminate.

        Unshelve.
        all: auto.
  Qed.

  (* TODO: Move this, prove this. *)
  Lemma int_to_ptr_succeeds_regardless_of_provenance :
    forall {pr1 pr2 addr ptr},
      LLVMParams64BitIntptr.ITOP.int_to_ptr addr pr1 = NoOom ptr ->
      exists ptr', LLVMParams64BitIntptr.ITOP.int_to_ptr addr pr2 = NoOom ptr'.
  Proof.
  Admitted.

  (* TODO: Move. Probably a better name for this. *)
  Lemma IntMap_find_NoOom_assoc_list' :
    forall {X Y} (l : list (IntMaps.IM.key * X)) (f : (IntMaps.IM.key * X) -> OOM (IntMaps.IM.key * Y)) m_elts (n : Z) (x : X),
      SetoidList.NoDupA (IntMaps.IM.eq_key (elt:=X)) l ->
      map_monad f l = NoOom m_elts ->
      (forall '(ix, x) '(ix', y), f (ix, x) = NoOom (ix', y) -> ix = ix') ->
      SetoidList.findA (IntMaps.IP.F.eqb n) l = Some x ->
      exists y,
        IntMaps.IM.find (elt:=Y) n (IntMaps.IP.of_list m_elts) = Some y /\
          NoOom (n, y) = f (n, x).
  Proof.
    induction l; intros f m_elts n x NODUP HMAPM F FIND.
    - cbn in *.
      inv HMAPM.
      cbn in *.
      inv FIND.
    - cbn in *.
      break_match_hyp; inv HMAPM.
      break_match_hyp; inv H0.
      break_match_hyp; inv H1.

      rename k into a_k.
      rename x0 into a_v.
      destruct p as [p_k p_v].
      pose proof (F (a_k, a_v) (p_k, p_v) Heqo); subst.
      Opaque IntMaps.IM.find.
      Opaque IntMaps.IM.add.
      cbn in *.
      break_match_hyp.
      + (* New element *)
        inv FIND.
        unfold IntMaps.IP.F.eqb in Heqb.
        break_match_hyp; inv Heqb.
        exists p_v.
        split; auto.
        unfold IntMaps.IP.uncurry.
        cbn.
        rewrite IntMaps.IP.F.add_eq_o; cbn; auto.
      + (* Old element *)
        inversion NODUP; subst.
        rename H1 into NIN.
        rename H2 into NODUP'.

        unfold IntMaps.IP.F.eqb in Heqb.
        break_match_hyp; inv Heqb.

        unfold IntMaps.IP.uncurry.
        rewrite IntMaps.IP.F.add_neq_o; cbn; auto.
  Qed.

  (* TODO: Move. Probably a better name for this. *)
  Lemma IntMap_find_NoOom_elements' :
    forall {X Y} (m : IntMaps.IM.t X) (f : (IntMaps.IM.key * X) -> OOM (IntMaps.IM.key * Y)) m_elts (n : Z) (x : X),
      map_monad f (IntMaps.IM.elements (elt:=X) m) = NoOom m_elts ->
      (forall '(ix, x) '(ix', y), f (ix, x) = NoOom (ix', y) -> ix = ix') ->
      IntMaps.IM.find (elt:=X) n m = Some x ->
      exists y,
        IntMaps.IM.find (elt:=Y) n (IntMaps.IP.of_list m_elts) = Some y /\
          NoOom (n, y) = f (n, x).
  Proof.
    intros X Y m f m_elts n x HMAPM F FIND.

    pose proof IntMaps.IP.F.elements_o.
    setoid_rewrite H.
    epose proof IntMap_find_NoOom_assoc_list' (IntMaps.IM.elements (elt:=X) m) f m_elts n x.
    forward H0.
    {
      apply IntMaps.IM.elements_3w.
    }
    specialize (H0 HMAPM F).
    forward H0.
    {
      rewrite <- H; auto.
    }

    destruct H0 as [y [FINDY RES]].
    exists y.
    split; auto.

    rewrite <- IntMaps.IP.F.elements_o; auto.
  Qed.

  Lemma fin_inf_allocations_preserved :
    forall ms_fin ms_inf ms_fin' ms_inf',
      MemState_refine_prop ms_inf ms_fin ->
      MemState_refine_prop ms_inf' ms_fin' ->
      Memory64BitIntptr.MMEP.MemSpec.allocations_preserved ms_fin ms_fin' ->
      MemoryBigIntptr.MMEP.MemSpec.allocations_preserved ms_inf ms_inf'.
  Proof.
    intros ms_fin ms_inf ms_fin' ms_inf' REF REF' ALLOCS_PRESERVED.
    red.
    intros ptr aid.
    split; intros BYTE_ALLOCATED.
    - destruct (InfToFinAddrConvert.addr_convert ptr) eqn:PTRCONV.
      + eapply fin_inf_byte_allocated; eauto.
        red in ALLOCS_PRESERVED.
        eapply ALLOCS_PRESERVED.
        eapply inf_fin_byte_allocated; eauto.
      + (* This should be a contradiction based on ptr / BYTE_ALLOCATED *)
        exfalso.
        eapply inf_fin_big_address_byte_not_allocated.
        apply REF.
        all: eauto.
    - destruct (InfToFinAddrConvert.addr_convert ptr) eqn:PTRCONV.
      + eapply fin_inf_byte_allocated; eauto.
        red in ALLOCS_PRESERVED.
        eapply ALLOCS_PRESERVED.
        eapply inf_fin_byte_allocated; eauto.
      + (* This should be a contradiction based on ptr / BYTE_ALLOCATED *)
        exfalso.
        eapply inf_fin_big_address_byte_not_allocated.
        apply REF'.
        all: eauto.
  Qed.


  Lemma inf_frame_eqv_empty_l :
    forall f,
      MemoryBigIntptr.MMEP.MMSP.frame_eqv [] f ->
      f = [].
  Proof.
    intros f EQV.
    destruct f; auto.
    red in  EQV.
    specialize (EQV a).
    destruct EQV.
    forward H0; cbn; auto.
    red in H0.
    cbn in H0.
    contradiction.
  Qed.

  Lemma inf_frame_eqv_empty_r :
    forall f,
      MemoryBigIntptr.MMEP.MMSP.frame_eqv f [] ->
      f = [].
  Proof.
    intros f EQV.
    symmetry in EQV.
    apply inf_frame_eqv_empty_l.
    auto.
  Qed.

  Lemma fin_ptr_to_int_in_bounds:
    forall (ptr : FinAddr.addr),
          in_bounds (LLVMParams64BitIntptr.PTOI.ptr_to_int ptr) = true.
  Proof.
    intros.
    destruct ptr.
    unfold LLVMParams64BitIntptr.PTOI.ptr_to_int. cbn.
    eapply in_bounds_exists_addr.
    exists (i,p); auto.
  Qed.

    
  (*
    This version may not be true.
   *)
  (*
  Lemma find_ptr_to_int_lift_Heap_gen :
    forall h ptr b,
      IntMaps.IM.find ptr (lift_Heap h) = Some (lift_Block b) ->
        (IntMaps.IM.find ptr h) = Some b.
  Proof.
    intros.
    unfold lift_Heap in H.
    apply IntMaps.IP.F.find_mapsto_iff in H.
    apply IntMaps.IP.F.find_mapsto_iff.
    apply IntMaps.IP.F.map_mapsto_iff in H.
    destruct H as [x [EQ HX]].
    apply MapsTo_filter_dom_true in HX.
  Qed.
  *)
  
  Lemma find_ptr_to_int_lift_Heap :
    forall h ptr,
      IntMaps.IM.find (LLVMParams64BitIntptr.PTOI.ptr_to_int ptr) (lift_Heap h) =
        option_map lift_Block (IntMaps.IM.find (LLVMParams64BitIntptr.PTOI.ptr_to_int ptr) h).
  Proof.
    intros.
    unfold lift_Heap.
    
    unfold option_map.
    break_match.
    - apply IntMaps.IP.F.find_mapsto_iff in Heqo.
      apply IntMaps.IP.F.find_mapsto_iff.
      apply IntMaps.IP.F.map_mapsto_iff.
      exists b. split; auto.
      apply MapsTo_filter_dom_true; auto.
      apply fin_ptr_to_int_in_bounds.
    - rewrite IntMaps.IP.F.map_o.
      apply (find_filter_dom_None in_bounds) in Heqo.
      rewrite Heqo.
      reflexivity.
  Qed.
      
  (* TODO: Move this *)
  Lemma ptr_in_heap_prop_lift :
    forall h root ptr,
      FinMem.MMEP.MMSP.ptr_in_heap_prop h root ptr ->
      InfMem.MMEP.MMSP.ptr_in_heap_prop (lift_Heap h) (fin_to_inf_addr root) (fin_to_inf_addr ptr).
  Proof.
    intros h root ptr IN.
    red in *.
    rewrite fin_to_inf_addr_ptr_to_int.
    rewrite find_ptr_to_int_lift_Heap.

    destruct (IntMaps.IM.find (elt:=FinMem.MMEP.MMSP.Block) (LLVMParams64BitIntptr.PTOI.ptr_to_int root) h) eqn: EQ; simpl in *.
    - unfold lift_Block.
      apply in_map_iff in IN.
      destruct IN as [addr [EQ' HI]].
      apply in_map_iff.
      exists (fin_to_inf_addr addr).
      split.
      rewrite fin_to_inf_addr_ptr_to_int.
      rewrite fin_to_inf_addr_ptr_to_int.
      assumption.
      apply in_map.
      assumption.
    - contradiction.
  Qed.

  (* TODO: Move this *)
  Lemma ptr_in_heap_prop_lift_inv :
    forall {h root_inf root_fin ptr_inf},
      InfMem.MMEP.MMSP.ptr_in_heap_prop (lift_Heap h) root_inf ptr_inf ->
      InfToFinAddrConvert.addr_convert root_inf = NoOom root_fin ->
      exists ptr_fin,
        InfToFinAddrConvert.addr_convert ptr_inf = NoOom ptr_fin /\
          FinMem.MMEP.MMSP.ptr_in_heap_prop h root_fin ptr_fin.
  Proof.
    intros h root_inf root_fin ptr_inf IN CONV.
    red in IN.
    unfold lift_Heap, lift_Block in IN.
    unfold FinMem.MMEP.MMSP.ptr_in_heap_prop.

    rewrite IntMaps.IP.F.map_o in IN.
    break_match_hyp; try contradiction.
    apply Util.option_map_some_inv in Heqo as (?&?&?).

    erewrite fin_inf_ptoi; eauto.
    apply find_filter_dom_true in H.
    destruct H as [H HB].
    rewrite H.

    generalize dependent b.
    clear H.
    induction x; intros b H0 IN.
    - cbn in *.
      inv H0.
      cbn in *.
      contradiction.
    - cbn in *.
      inv H0.
      destruct IN as [IN | IN].
      + destruct a.
        destruct ptr_inf.
        exists (i, p0).
        split; auto.
        {
          rewrite fin_to_inf_addr_ptr_to_int in IN.
          cbn in IN.
          unfold LLVMParams64BitIntptr.PTOI.ptr_to_int in IN.
          cbn in IN; subst.

          cbn.
          unfold FinITOP.int_to_ptr.
          break_match.
          {
            pose proof Integers.Int64.unsigned_range i.
            lia.
          }

          rewrite Int64.repr_unsigned.
          auto.
        }
      + rewrite List.map_map in IN.
        apply in_map_iff in IN.
        pose proof IN as IN'.
        destruct IN as (?&?&?).

        specialize (IHx _ eq_refl).
        forward IHx.
        { rewrite List.map_map.
          apply in_map_iff.
          auto.
        }

        destruct IHx as (?&?&?).
        exists x1.
        split; auto.
  Qed.


  Lemma MapsTo_filter_dom_subset_strong :
    forall {A} x v f (m : IntMaps.IntMap A),
    IntMaps.IM.MapsTo x v (IntMaps.IP.filter_dom f m) ->
    IntMaps.IM.MapsTo x v m /\ f x = true.
  Proof.
    intros.
    apply IntMaps.IP.filter_iff in H; auto.
    repeat red; intros; subst; auto.
  Qed.

  Lemma In_MapsTo_exists :
    forall {A} x (m : IntMaps.IntMap A),
      IntMaps.IM.In x m <->
        exists v, IntMaps.IM.MapsTo x v m.
  Proof.
    intros.
    split; intros.
    - rewrite IntMaps.IP.F.mem_in_iff in H.
      assert (IntMaps.member x m = true).
      unfold IntMaps.member. assumption.
      apply IntMaps.member_lookup in H0.
      destruct H0 as [v HV].
      exists v. unfold IntMaps.lookup in HV.
      apply IntMaps.IM.find_2 in HV.
      assumption.
    - destruct H as [v HV].
      rewrite IntMaps.IP.F.mem_in_iff.
      apply IntMaps.IM.find_1 in HV.
      eapply IntMaps.lookup_member.
      apply HV.
  Qed.
  
  (* (* TODO: Move this *) *)
  (* Definition heap_refine (h1 : InfMemMMSP.Heap) (h2 : FinMemMMSP.Heap) : Prop *)
  (*   := MemoryBigIntptr.MMEP.MemSpec.heap_preserved h1 (lift_Heap h2). *)

  (* TODO: Move this *)
  (* TODO: This may not be true... The roots are just keys in the map *)
  (*    for the heap, so nothing is forcing them to be in bounds for *)
  (*    finite memory... May be able to use MemState_refine_prop's *)
  (*    heap_preserved component to ensure this, though? *)
  (*  *)
  (* TODO: Will need the heap in bounds predicate *)
  Lemma root_in_heap_prop_lift_inv :
    forall {h root_inf},
      InfMem.MMEP.MMSP.root_in_heap_prop (lift_Heap h) root_inf ->
      exists root_fin,
        InfToFinAddrConvert.addr_convert root_inf = NoOom root_fin /\
        FinMem.MMEP.MMSP.root_in_heap_prop h root_fin.
  Proof.
    intros h root_inf IN.
    red in IN.
    apply IntMaps.member_lookup in IN.
    destruct IN as [v HV].
    unfold IntMaps.lookup in HV.
    unfold InfMem.MMEP.MMSP.Block in HV.
    unfold InfMemMMSP.Block in *.
    unfold lift_Heap in HV.
    apply IntMaps.IP.F.find_mapsto_iff in HV.
    apply filter_dom_map_eq in HV.
    apply MapsTo_filter_dom_subset_strong in HV.
    destruct HV as [HV IN].
    destruct root_inf.
    cbn in *.
    apply (in_bounds_exists_addr i p) in IN.
    destruct IN as [root_fin [HF EQ]].
    exists root_fin.
    split.
    - destruct root_fin. cbn in *.
      subst.
      apply LLVMParams64BitIntptr.ITOP.int_to_ptr_ptr_to_int. auto.
    - unfold FinMem.MMEP.MMSP.root_in_heap_prop.
      unfold IntMaps.member.
      apply IntMaps.IP.F.mem_in_iff.
      rewrite HF.
      apply IntMaps.IP.F.map_mapsto_iff in HV.
      destruct HV as [b [_ HIN]].
      apply In_MapsTo_exists.
      exists b.
      assumption.
  Qed.

  (* TODO: Move this *)
  Lemma heap_eqv_lift :
    forall h1 h2,
      FinMem.MMEP.MMSP.heap_eqv h1 h2 ->
      InfMem.MMEP.MMSP.heap_eqv (lift_Heap h1) (lift_Heap h2).
  Proof.
    intros h1 h2 EQV.
    destruct EQV.

    split.
    - (* Roots *)
      intros ptr.
      split; intros IN.
      + apply root_in_heap_prop_lift_inv in IN.
        destruct IN as (ptr_fin & CONV & IN).
        apply EQV in IN.
        apply ptr_in_heap_prop_lift in IN.
        erewrite fin_to_inf_addr_conv_inf in IN; eauto.
      + apply ptr_in_heap_prop_lift_inv in IN.
        destruct IN as (ptr_fin & CONV & IN).
        apply EQV in IN.
        apply ptr_in_heap_prop_lift in IN.
        erewrite fin_to_inf_addr_conv_inf in IN; eauto.

    - (* Pointers *)


    intros ptr.
    split; intros IN.
    - apply ptr_in_frame_prop_lift_inv in IN.
      destruct IN as (ptr_fin & CONV & IN).
      apply EQV in IN.
      apply ptr_in_frame_prop_lift in IN.
      erewrite fin_to_inf_addr_conv_inf in IN; eauto.
    - apply ptr_in_frame_prop_lift_inv in IN.
      destruct IN as (ptr_fin & CONV & IN).
      apply EQV in IN.
      apply ptr_in_frame_prop_lift in IN.
      erewrite fin_to_inf_addr_conv_inf in IN; eauto.


    intros fs1 fs2 EQV.
    red in *.
    intros f n.
    split; intros FSE.
    - apply FSNth_eqv_lift_inv in FSE.
      destruct FSE as (f_fin & F & FSE).

      rewrite <- F.
      apply FSNth_eqv_lift.
      apply EQV.
      auto.
    - apply FSNth_eqv_lift_inv in FSE.
      destruct FSE as (f_fin & F & FSE).

      rewrite <- F.
      apply FSNth_eqv_lift.
      apply EQV.
      auto.
  Qed.

  (* (* TODO: Move this *) *)
  (* Lemma frame_stack_eqv_lift_inv : *)
  (*   forall fs1 fs2, *)
  (*     InfMem.MMEP.MMSP.frame_stack_eqv fs1 fs2 -> *)
  (*     exists fs1_fin fs2_fin, *)
  (*       fs1 = lift_FrameStack fs1_fin /\ *)
  (*         fs2 = lift_FrameStack fs2_fin /\ *)
  (*         FinMem.MMEP.MMSP.frame_stack_eqv fs1_fin fs2_fin. *)
  (* Proof. *)
  (* Admitted. *)

  (* TODO: Move this *)
  Lemma memory_stack_frame_stack_prop_lift :
    forall ms_fin fs_fin,
      FinMem.MMEP.MMSP.memory_stack_frame_stack_prop ms_fin fs_fin ->
      InfMem.MMEP.MMSP.memory_stack_frame_stack_prop (lift_memory_stack ms_fin) (lift_FrameStack fs_fin).
  Proof.
    intros ms_fin fs_fin FSP.
    red in FSP; red.
    destruct ms_fin.
    cbn in *.
    apply frame_stack_eqv_lift.
    auto.
  Qed.

  (* TODO: Move this *)
  Lemma memory_stack_frame_stack_prop_lift_inv :
    forall ms_inf fs_inf,
      InfMem.MMEP.MMSP.memory_stack_frame_stack_prop ms_inf fs_inf ->
      exists ms_fin fs_fin,
        ms_inf = lift_memory_stack ms_fin /\
          fs_inf = lift_FrameStack fs_fin /\
          FinMem.MMEP.MMSP.memory_stack_frame_stack_prop ms_fin fs_fin.
  Proof.
    intros ms_inf fs_inf FSP.
    red in FSP.
  Admitted.

  (* TODO: Move this *)
  Lemma frame_stack_preserved_lift_MemState :
    forall ms_fin ms_fin',
      FinMem.MMEP.MemSpec.frame_stack_preserved ms_fin ms_fin' ->
      InfMem.MMEP.MemSpec.frame_stack_preserved (lift_MemState ms_fin) (lift_MemState ms_fin').
  Proof.
    intros ms_fin ms_fin' FSP.
    red in FSP; red.
    destruct ms_fin, ms_fin'; cbn in *.
    intros fs.
    split; intros MSFSP.
    - red.
      apply memory_stack_frame_stack_prop_lift_inv in MSFSP.
      destruct MSFSP as (?&?&?&?&?); subst.
      apply memory_stack_frame_stack_prop_lift in H1.
      rewrite <- H in H1.
      apply memory_stack_frame_stack_prop_lift.
      apply FSP.
      apply memory_stack_frame_stack_prop_lift_inv in H1.
      auto.
      admit.
    - admit.
  Admitted.


  Lemma IntMap_member_map_keys_eq :
    forall {A B} (f : A -> B) m x,
      is_true (IntMaps.member x m) <->
        is_true (IntMaps.member x (IntMaps.IP.of_list (map (fun '(ix, a) => (ix, f a)) (IntMaps.IM.elements m)))).
  Proof.
    intros A B f m x.
    unfold IntMaps.member.
    unfold is_true.
    do 2 rewrite <- IntMaps.IP.F.mem_in_iff.

  Admitted.

  Lemma member_lift_Heap:
    forall ptr h,
      is_true (IntMaps.member ptr (lift_Heap h)) <-> is_true (IntMaps.member ptr h).
  Proof.
  Admitted.

  (* TODO: add Heap_in_bounds predicate for MemState and add that here *)
  Lemma fin_inf_root_in_heap_prop_lift :
    forall h root,
      (exists fin_root, (fin_to_inf_addr fin_root) = root /\ FinMem.MMEP.MMSP.root_in_heap_prop h fin_root) <->
        InfMem.MMEP.MMSP.root_in_heap_prop (lift_Heap h) root.
  Proof.
    intros h root.
    unfold FinMem.MMEP.MMSP.root_in_heap_prop.
    unfold InfMem.MMEP.MMSP.root_in_heap_prop.
    split; intros.
    - destruct H as [fin_root [HEQ H]].
      rewrite member_lift_Heap.
      rewrite <- HEQ.
      rewrite fin_to_inf_addr_ptr_to_int.
      assumption.
    - apply member_lift_Heap in H.
      unfold FinMem.MMEP.MMSP.Heap in *.

      apply (IntMap_member_map_keys_eq id) in H.
      destruct root.
      unfold LLVMParamsBigIntptr.PTOI.ptr_to_int in *.
      cbn in H.
      unfold FinAddr.addr.
      unfold FiniteAddresses.Iptr. unfold Iptr in i.
  Admitted.

  Lemma root_in_heap_prop_lift:
    forall h1 h2 : FinMem.MMEP.MMSP.Heap,
      (forall root : LLVMParams64BitIntptr.ADDR.addr,
          FinMem.MMEP.MMSP.root_in_heap_prop h1 root <-> FinMem.MMEP.MMSP.root_in_heap_prop h2 root) ->
      forall root : LLVMParamsBigIntptr.ADDR.addr,
        InfMem.MMEP.MMSP.root_in_heap_prop (lift_Heap h1) root ->
        InfMem.MMEP.MMSP.root_in_heap_prop (lift_Heap h2) root.
  Proof.
    intros h1 h2 heap_roots_eqv root HR.
    unfold lift_Heap.
    apply fin_inf_root_in_heap_prop_lift in HR.
    destruct HR as (fin_root  & HEQ & HR).
    subst.
    apply heap_roots_eqv in HR.


  Admitted.



  (* SAZ: need to update this *)
  (* TODO: Move this *)
  Lemma Heap_eqv_lift :
    forall h1 h2,
      FinMem.MMEP.MMSP.heap_eqv h1 h2 ->
      InfMem.MMEP.MMSP.heap_eqv (lift_Heap h1) (lift_Heap h2).
  Proof.
    intros h1 h2 H.
    inversion H.
    constructor; intros; split; intros.
    - eapply root_in_heap_prop_lift.
      apply heap_roots_eqv.
      assumption.
    - eapply root_in_heap_prop_lift.
      intros.
      symmetry.
      apply heap_roots_eqv.
      assumption.

    - admit.
  Admitted.


  Lemma memory_stack_heap_prop_lift :
    forall ms_fin h_fin,
      FinMem.MMEP.MMSP.memory_stack_heap_prop ms_fin h_fin ->
      InfMem.MMEP.MMSP.memory_stack_heap_prop (lift_memory_stack ms_fin) (lift_Heap h_fin).
  Proof.
    intros ms_fin h_fin MSH.
    red in MSH; red.
    destruct ms_fin.
    cbn in *.
  Admitted.

  (* SAZ: work on this *)
  (* TODO: Move this *)
  Lemma heap_preserved_lift_MemState :
    forall ms_fin ms_fin',
      FinMem.MMEP.MemSpec.heap_preserved ms_fin ms_fin' ->
      InfMem.MMEP.MemSpec.heap_preserved (lift_MemState ms_fin) (lift_MemState ms_fin').
  Proof.
    intros ms_fin ms_fin' HP.
    red in HP.
    red.
    destruct ms_fin, ms_fin'; cbn in *.
    intros h.
    split; intros MSFSP.
    -


(*
      apply memory_heap_prop_lift_inv in MSFSP.
      destruct MSFSP as (?&?&?&?&?); subst.
      apply memory_stack_frame_stack_prop_lift in H1.
      rewrite <- H in H1.
      apply memory_stack_frame_stack_prop_lift.
      apply FSP.
      apply memory_stack_frame_stack_prop_lift_inv in H1.
      auto.
      admit.
    - admit.
*)
  Admitted.


  (* TODO: Move this *)
  Lemma convert_Frame_cons :
    forall ptr f,
      convert_Frame (ptr :: f) = a' <- InfToFinAddrConvert.addr_convert ptr;; f' <- convert_Frame f;; ret (a' :: f').
  Proof.
    intros ptr f.
    cbn.
    break_match; auto.
  Qed.

  Lemma frame_eqv_cons_cons :
    forall f1 f2 a,
      (* This isn't true... f1 could have no a, but f2 could already have an a... UGGGH. *)
      Memory64BitIntptr.MMEP.MMSP.frame_eqv (a :: f1) (a :: f2) ->
      Memory64BitIntptr.MMEP.MMSP.frame_eqv f1 f2.
  Proof.
  Abort.


  (* Lemma convert_Frame_eqv_cons_rev : *)
  (*   forall {f_inf f_fin a_inf a_fin f_fin'}, *)
  (*     convert_Frame f_inf = NoOom f_fin -> *)
  (*     InfToFinAddrConvert.addr_convert a_inf = NoOom a_fin -> *)
  (*     Memory64BitIntptr.MMEP.MMSP.frame_eqv (a_fin :: f_fin') f_fin -> *)
  (*     exists f_inf' f_fin'', *)
  (*       MemoryBigIntptr.MMEP.MMSP.frame_eqv (a_inf :: f_inf') f_inf /\ *)
  (*         convert_Frame f_inf' = NoOom f_fin'' /\ *)
  (*         Memory64BitIntptr.MMEP.MMSP.frame_eqv f_fin' f_fin''. *)
  (* Proof. *)
  (*   intros f_inf f_fin a_inf a_fin f_fin' CONV ADDR_CONV EQV. *)

  (*   Lemma convert_Frame_eqv_rev : *)
  (*   forall {f_fin' f_inf f_fin}, *)
  (*     convert_Frame f_inf = NoOom f_fin -> *)
  (*     Memory64BitIntptr.MMEP.MMSP.frame_eqv f_fin f_fin' -> *)
  (*     exists f_inf', convert_Frame f_inf' = NoOom f_fin'. *)
  (*   Proof. *)
  (*     induction f_fin'; intros f_inf f_fin CONV EQV. *)
  (*     - inv CONV. *)
  (*       exists []. *)
  (*       apply frame_eqv_empty_r in EQV. *)
  (*       subst. *)
  (*       reflexivity. *)
  (*     - assert (exists a_inf, InfToFinAddrConvert.addr_convert a_inf = NoOom a) as ADDR_CONV. *)
  (*       { *)
  (*         destruct (InfITOP.int_to_ptr (FinPTOI.ptr_to_int a) (FinPROV.address_provenance a)) eqn:PTR. *)
  (*         - exists a0. *)
  (*           unfold InfToFinAddrConvert.addr_convert. *)
  (*           destruct a0. *)
  (*           cbn in *. *)
  (*           inv PTR. *)
  (*           apply LLVMParams64BitIntptr.ITOP.int_to_ptr_ptr_to_int; auto. *)
  (*         - pose proof InfITOP_BIG.int_to_ptr_safe (FinPTOI.ptr_to_int a) (FinPROV.address_provenance a). *)
  (*           rewrite PTR in H. *)
  (*           contradiction. *)
  (*       } *)
  (*       destruct ADDR_CONV as [a_inf ADDR_CONV]. *)

  (*       assert (exists f_inf', convert_Frame f_inf' = NoOom f_fin') as (f_inf' & FINF). *)
  (*       { *)
  (*         (* Because of EQV I know that every element in *)
   (*            f_fin' is also an element of f_fin... *)

   (*            If something is an element of f_fin, then there *)
   (*            exists a convertible infinite element. *)
   (*          *) *)
  (*         admit. *)
  (*       } *)

  (*       exists (a_inf :: f_inf'). *)
  (*       rewrite convert_Frame_cons. *)
  (*       rewrite ADDR_CONV. *)
  (*       rewrite FINF. *)
  (*       cbn. *)
  (*       reflexivity. *)
  (*   Admitted. *)

  (*   symmetry in EQV. *)
  (*   pose proof convert_Frame_eqv_rev CONV EQV as (f_inf' & CONV'). *)
  (*   exists f_inf'. exists (a_fin :: f_fin'). *)
  (*   split; [|split]; auto. *)
  (*   symmetry; auto. *)
  (* Qed. *)

  (* TODO: Move this to frame library *)
  Lemma frame_eqv_cons :
    forall a f1 f2,
      MemoryBigIntptr.MMEP.MMSP.frame_eqv f1 f2 ->
      MemoryBigIntptr.MMEP.MMSP.frame_eqv (a :: f1) (a :: f2).
  Proof.
    intros a f1 f2 H.
    rewrite H.
    reflexivity.
  Qed.

  Lemma convert_Frame_cons_rev :
    forall f_inf f_fin a_fin ,
      convert_Frame f_inf = NoOom (a_fin :: f_fin) ->
      exists f_inf' a_inf,
        f_inf = a_inf :: f_inf' /\
          InfToFinAddrConvert.addr_convert a_inf = NoOom a_fin.
  Proof.
    destruct f_inf; intros f_fin a_fin CONV.
    - cbn in CONV.
      inv CONV.
    - rewrite convert_Frame_cons in CONV.
      cbn in CONV.
      break_match_hyp; inv CONV.
      break_match_hyp; inv H0.
      exists f_inf. exists a.
      split; auto.
  Qed.

  Lemma frame_eqv_Add :
    forall {a f1 f2},
      Memory64BitIntptr.MMEP.MMSP.frame_eqv (a :: f1) f2 ->
      exists f, Add a f f2.
  Proof.
  Admitted.

  Lemma convert_Frame_eqv_rev :
    forall f_inf f_inf' f_fin f_fin',
      convert_Frame f_inf = NoOom f_fin ->
      convert_Frame f_inf' = NoOom f_fin' ->
      Memory64BitIntptr.MMEP.MMSP.frame_eqv f_fin f_fin' ->
      MemoryBigIntptr.MMEP.MMSP.frame_eqv f_inf f_inf'.
  Proof.
    induction f_inf; intros f_inf' f_fin f_fin' H H0 H1.
    - cbn in *.
      inv H.

      apply frame_eqv_empty_l in H1; subst.
      destruct f_inf'; [reflexivity|].
      cbn in H0.
      break_match_hyp; inv H0.
      break_match_hyp; inv H1.
    - rewrite convert_Frame_cons in H.
      cbn in H.
      break_match_hyp; inv H.
      break_match_hyp; inv H3.

      (* Want to pull out the 'a' from f_inf'

             f_inf' ≈ a :: f_inf''

             Order may be different >:C.

             exists f_inf'', Add a f_inf' f_inf''
       *)

      pose proof frame_eqv_Add H1 as [f' ADD].

      induction ADD.
      + pose proof H0.
        apply convert_Frame_cons_rev in H0.
        destruct H0 as (?&?&?&?).
        subst.
        rewrite convert_Frame_cons in H.
        cbn in H.
        rewrite H2 in H.
        break_match_hyp; inv H.

        eapply IHf_inf in Heqo1; auto.
        rewrite Heqo1.
        --
          assert (LLVMParamsBigIntptr.PTOI.ptr_to_int a = LLVMParamsBigIntptr.PTOI.ptr_to_int x0).
          { erewrite <- fin_inf_ptoi; [|exact Heqo].
            erewrite <- fin_inf_ptoi; [|exact H2].
            auto.
          }

          red. cbn.
          rewrite H.
          tauto.
        -- (* pose proof convert_Frame_eqv_cons_rev H0 Heqo H1 as (f_inf'' & f_fin'' & EQV1 & CONV & EQV2). *)
          (* rewrite <- EQV1. *)

          (* apply frame_eqv_cons. *)
          (* eapply IHf_inf; auto; eauto. *)

          (* (* QED *) *)

          (* eauto. *)
          (* reflexivity. *)
          (* red. *)
          (* rewrite EQV *)

          (* (* Probably want to use this *) *)
          (* (* Add_inv: forall [A : Type] (a : A) (l : list A), In a l -> exists l' : list A, Add a l' l *) *)

          (* (* TODO: Move this to MMSP or something *) *)
          (* Lemma frame_eqv_cons_l : *)
          (*   forall f' f a, *)
          (*     Memory64BitIntptr.MMEP.MMSP.frame_eqv (a :: f) f' -> *)
          (*     exists f'', *)
          (*       Memory64BitIntptr.MMEP.MMSP.frame_eqv f' (a :: f'') /\ *)
          (*         Memory64BitIntptr.MMEP.MMSP.frame_eqv f f''. *)
          (* Proof. *)
          (*   induction f'; intros f ptr EQV. *)
          (*   - apply frame_eqv_empty_r in EQV. *)
          (*     inv EQV. *)
  (*   - (* Unknown whether a = ptr... *)

   (*        If a = ptr, then f'' = f', and we're done. *)
   (*      *) *)
          (*     pose proof (FinLP.ADDR.eq_dec a ptr) as [EQ | NEQ]; subst. *)
          (*     + exists f'. *)
          (*       split; try reflexivity. *)
          (*       (* I guess I don't know if ptr is duplicated in ONE of f / f'... *) *)
          (* Admitted. *)

          (* apply frame_eqv_cons_l in H1. *)
          (* destruct H1 as (?&?&?). *)

          (* symmetry in H. *)
          (* apply frame_eqv_cons_l in H. *)
          (* destruct H as (?&?&?). *)

          (* rewrite <- H1 in H. *)
  Admitted.

  Lemma convert_FrameStack_eqv_rev :
    forall fs_inf fs_inf' fs_fin fs_fin',
      convert_FrameStack fs_inf = NoOom fs_fin ->
      convert_FrameStack fs_inf' = NoOom fs_fin' ->
      Memory64BitIntptr.MMEP.MMSP.frame_stack_eqv fs_fin fs_fin' ->
      MemoryBigIntptr.MMEP.MMSP.frame_stack_eqv fs_inf fs_inf'.
  Proof.
    induction fs_inf; intros fs_inf' fs_fin fs_fin' FS1 FS2 EQV.
    - cbn in FS1.
      break_match_hyp; inv FS1.
      apply Memory64BitIntptr.MMEP.MMSP.frame_stack_inv in EQV as [EQV | EQV].
      {
        destruct EQV as (?&?&?&?&?&?&?&?).
        inv H.
      }

      destruct EQV as (?&?&?&?&?).
      subst.

      destruct fs_inf'.
      2: {
        cbn in FS2.
        break_match_hyp; inv FS2.
        break_match_hyp; inv H2.
      }

      cbn in FS2.
      break_match_hyp; inv FS2.
      inv H.
  Admitted.

  (* TODO: Move this *)
  Lemma MemState_refine_prop_frame_stack_preserved :
    forall ms_inf ms_fin,
      MemState_refine_prop ms_inf ms_fin ->
      InfMem.MMEP.MemSpec.frame_stack_preserved ms_inf (lift_MemState ms_fin).
  Proof.
    intros ms_inf ms_fin MSR.
    red in MSR.
    tauto.
  Qed.

  (* TODO: Move this *)
  Lemma MemState_refine_prop_allocations_preserved :
    forall {ms_inf ms_fin},
      MemState_refine_prop ms_inf ms_fin ->
      InfMem.MMEP.MemSpec.allocations_preserved ms_inf (lift_MemState ms_fin).
  Proof.
    intros ms_inf ms_fin MSR.
    red in MSR.
    tauto.
  Qed.

  Lemma fin_inf_frame_stack_preserved :
    forall ms_fin ms_inf ms_fin' ms_inf',
      MemState_refine_prop ms_inf ms_fin ->
      MemState_refine_prop ms_inf' ms_fin' ->
      Memory64BitIntptr.MMEP.MemSpec.frame_stack_preserved ms_fin ms_fin' ->
      MemoryBigIntptr.MMEP.MemSpec.frame_stack_preserved ms_inf ms_inf'.
  Proof.
    intros ms_fin ms_inf ms_fin' ms_inf' REF REF' FSP_FIN.

    apply MemState_refine_prop_frame_stack_preserved in REF, REF'.
    red in REF, REF', FSP_FIN.
    red.

    intros fs.
    split; intros FSP_INF.
    - red. red in FSP_INF.
      rewrite <- FSP_INF.
      apply REF'.
      red.
      symmetry.
      apply REF.

      pose proof frame_stack_preserved_lift_MemState ms_fin ms_fin'.
      forward H; auto.
      red in H.
      apply H.

      destruct ms_fin', ms_memory_stack; cbn.
      red. cbn.
      reflexivity.
    - red. red in FSP_INF.
      rewrite <- FSP_INF.
      apply REF.
      red.
      symmetry.
      apply REF'.

      pose proof frame_stack_preserved_lift_MemState ms_fin ms_fin'.
      forward H; auto.
      red in H.
      apply H.

      destruct ms_fin, ms_memory_stack; cbn.
      red. cbn.
      reflexivity.
  Qed.

  (* TODO: Move this *)
  Lemma convert_FrameStack_Snoc_equation :
    forall fs f,
      convert_FrameStack (MemoryBigIntptr.MMEP.MMSP.Snoc fs f) =
        f' <- convert_Frame f;;
        fs' <- convert_FrameStack fs;;
        ret (Memory64BitIntptr.MMEP.MMSP.Snoc fs' f').
  Proof.
    intros fs.
    induction fs; intros f'; cbn; auto.
  Qed.

  (* TODO: Move this *)
  Lemma convert_FrameStack_snoc :
    forall {fs_inf f_inf fs_fin f_fin},
      convert_FrameStack fs_inf = NoOom fs_fin ->
      convert_Frame f_inf = NoOom f_fin ->
      convert_FrameStack (MemoryBigIntptr.MMEP.MMSP.Snoc fs_inf f_inf) = NoOom (Memory64BitIntptr.MMEP.MMSP.Snoc fs_fin f_fin).
  Proof.
    intros fs_inf f_inf fs_fin f_fin FS F.
    rewrite convert_FrameStack_Snoc_equation.
    rewrite F, FS.
    cbn.
    reflexivity.
  Qed.

  (* TODO: Move this *)
  Lemma MemState_refine_prop_heap_preserved :
    forall ms_inf ms_fin,
      MemState_refine_prop ms_inf ms_fin ->
      InfMem.MMEP.MemSpec.heap_preserved ms_inf (lift_MemState ms_fin).
  Proof.
    intros ms_inf ms_fin MSR.
    red in MSR.
    tauto.
  Qed.


  (* SAZ TODO: try these *)
  Lemma fin_inf_heap_preserved :
    forall ms_fin ms_inf ms_fin' ms_inf',
      MemState_refine_prop ms_inf ms_fin ->
      MemState_refine_prop ms_inf' ms_fin' ->
      Memory64BitIntptr.MMEP.MemSpec.heap_preserved ms_fin ms_fin' ->
      MemoryBigIntptr.MMEP.MemSpec.heap_preserved ms_inf ms_inf'.
  Proof.
    intros ms_fin ms_inf ms_fin' ms_inf' REF REF' HP.
    apply MemState_refine_prop_heap_preserved in REF, REF'.
    red.
    intros h.
    split; intros HP_INF.
    - red. red in HP_INF.
      rewrite <- HP_INF.
      red in REF, REF'.
      unfold InfMem.MMEP.MMSP.memory_stack_heap_prop in REF'.
      apply REF'.
      symmetry.
      apply REF.
      red.

      pose proof heap_preserved_lift_MemState ms_fin ms_fin'.
      apply H.
      + assumption.
      + red. reflexivity.
    - red. red in HP_INF.
      rewrite <- HP_INF.
      red in REF, REF'.
      unfold InfMem.MMEP.MMSP.memory_stack_heap_prop in REF'.
      apply REF.
      red.
      symmetry.
      apply REF'.

      pose proof heap_preserved_lift_MemState ms_fin ms_fin'.
      apply H.
      + assumption.
      + red. reflexivity.
  Qed.

  Lemma MemState_refine_prop_read_byte_allowed_all_preserved :
    forall ms_inf ms_fin,
      MemState_refine_prop ms_inf ms_fin ->
      InfMem.MMEP.MemSpec.read_byte_allowed_all_preserved ms_inf (lift_MemState ms_fin).
  Proof.
    intros ms_inf ms_fin MSR.
    red in MSR.
    tauto.
  Qed.


  Lemma fin_inf_read_byte_allowed_all_preserved :
    forall ms_fin ms_inf ms_fin' ms_inf',
      MemState_refine_prop ms_inf ms_fin ->
      MemState_refine_prop ms_inf' ms_fin' ->
      Memory64BitIntptr.MMEP.MemSpec.read_byte_allowed_all_preserved ms_fin ms_fin' ->
      MemoryBigIntptr.MMEP.MemSpec.read_byte_allowed_all_preserved ms_inf ms_inf'.
  Proof.
    intros ms_fin ms_inf ms_fin' ms_inf' REF REF' RBA.
    apply MemState_refine_prop_read_byte_allowed_all_preserved in REF, REF'.
    red.
    intros h.
    split; intros HP_INF.
    - red. red in HP_INF.
      destruct HP_INF as [aid [HA1 HA2]].
      exists aid. split; auto.
      red in REF, REF'.

  Admitted.

  Lemma fin_inf_read_byte_prop_all_preserved :
    forall ms_fin ms_inf ms_fin' ms_inf',
      MemState_refine_prop ms_inf ms_fin ->
      MemState_refine_prop ms_inf' ms_fin' ->
      Memory64BitIntptr.MMEP.MemSpec.read_byte_prop_all_preserved ms_fin ms_fin' ->
      MemoryBigIntptr.MMEP.MemSpec.read_byte_prop_all_preserved ms_inf ms_inf'.
  Proof.
    intros ms_fin ms_inf ms_fin' ms_inf' REF REF' RBP.
  Admitted.

  Lemma fin_inf_write_byte_allowed_all_preserved :
    forall ms_fin ms_inf ms_fin' ms_inf',
      MemState_refine_prop ms_inf ms_fin ->
      MemState_refine_prop ms_inf' ms_fin' ->
      Memory64BitIntptr.MMEP.MemSpec.write_byte_allowed_all_preserved ms_fin ms_fin' ->
      MemoryBigIntptr.MMEP.MemSpec.write_byte_allowed_all_preserved ms_inf ms_inf'.
  Proof.
    intros ms_fin ms_inf ms_fin' ms_inf' REF REF' HP.
  Admitted.

  Lemma fin_inf_free_byte_allowed_all_preserved :
    forall ms_fin ms_inf ms_fin' ms_inf',
      MemState_refine_prop ms_inf ms_fin ->
      MemState_refine_prop ms_inf' ms_fin' ->
      Memory64BitIntptr.MMEP.MemSpec.free_byte_allowed_all_preserved ms_fin ms_fin' ->
      MemoryBigIntptr.MMEP.MemSpec.free_byte_allowed_all_preserved ms_inf ms_inf'.
  Proof.
    intros ms_fin ms_inf ms_fin' ms_inf' REF REF' HP.
  Admitted.

  Lemma fin_inf_preserve_allocation_ids :
    forall ms_fin ms_inf ms_fin' ms_inf',
      MemState_refine_prop ms_inf ms_fin ->
      MemState_refine_prop ms_inf' ms_fin' ->
      Memory64BitIntptr.MMEP.MemSpec.preserve_allocation_ids ms_fin ms_fin' ->
      MemoryBigIntptr.MMEP.MemSpec.preserve_allocation_ids ms_inf ms_inf'.
  Proof.
    intros ms_fin ms_inf ms_fin' ms_inf' REF REF' HP.
  Admitted.

  Lemma fin_inf_write_byte_operation_invariants :
    forall addr_inf addr_fin ms_fin ms_inf ms_fin' ms_inf',
      MemState_refine_prop ms_inf ms_fin ->
      MemState_refine_prop ms_inf' ms_fin' ->
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      Memory64BitIntptr.MMEP.MemSpec.write_byte_operation_invariants ms_fin ms_fin' ->
      MemoryBigIntptr.MMEP.MemSpec.write_byte_operation_invariants ms_inf ms_inf'.
  Proof.
    intros addr_inf addr_fin ms_fin ms_inf ms_fin' ms_inf' REF REF' CONV INV.
    destruct INV.
    split.

    - eapply fin_inf_allocations_preserved; eauto.
    - eapply fin_inf_frame_stack_preserved; eauto.
    - eapply fin_inf_heap_preserved; eauto.
    - eapply fin_inf_read_byte_allowed_all_preserved; eauto.
    - eapply fin_inf_write_byte_allowed_all_preserved; eauto.
    - eapply fin_inf_free_byte_allowed_all_preserved; eauto.
    - eapply fin_inf_preserve_allocation_ids; eauto.
  Qed.

  Lemma write_byte_spec_MemPropT_Heap_in_bounds :
    forall ms_fin ms_fin' addr_fin byte_fin res_fin,
      Heap_in_bounds ms_fin ->
      Memory64BitIntptr.MMEP.MemSpec.write_byte_spec_MemPropT addr_fin byte_fin
        ms_fin
        (ret (ms_fin', res_fin)) ->
      Heap_in_bounds ms_fin'.
  Proof.
    intros ms_fin ms_fin' addr_fin byte_fin res_fin H H0.
    unfold Heap_in_bounds in *.
    intros.
    specialize (H i).
    apply H.
    unfold Memory64BitIntptr.MMEP.MemSpec.write_byte_spec_MemPropT in H0.
    red in H0. cbn in H0.
    (* should follow from write_byte_spec ? *)
  Admitted.

  Lemma fin_inf_write_byte_spec_MemPropT :
    forall {addr_fin addr_inf ms_fin ms_fin' ms_inf byte_inf byte_fin res_fin},
      (* TODO - QUESTION - which should be declared in bounds and which should be derived to be.
         SAZ: I think that Heap_in_bounds ms_fin' should be implied by
              write_byte_spec_MemPropT
       *)
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      sbyte_refine byte_inf byte_fin ->
      Memory64BitIntptr.MMEP.MemSpec.write_byte_spec_MemPropT addr_fin byte_fin
        ms_fin
        (ret (ms_fin', res_fin)) ->
      exists res_inf ms_inf',
        MemoryBigIntptr.MMEP.MemSpec.write_byte_spec_MemPropT addr_inf byte_inf ms_inf (ret (ms_inf', res_inf)) /\
          res_inf = res_fin /\
          MemState_refine_prop ms_inf' ms_fin'.
  Proof.
    intros addr_fin addr_inf ms_fin ms_fin' ms_inf byte_inf byte_fin [] MSR ADDR_CONV BYTE_REF WBP.
    assert (Heap_in_bounds ms_fin') as HIB.
    { eapply write_byte_spec_MemPropT_Heap_in_bounds.
      apply MSR.
      apply WBP.
    }
    destruct WBP.
    pose proof fin_inf_set_byte_memory HIB MSR ADDR_CONV BYTE_REF byte_written as (ms_inf' & SET_INF & MSR').

    exists tt. exists ms_inf'.
    split; auto.

    split; auto.
    - eapply fin_inf_write_byte_allowed; eauto.
    - eapply fin_inf_write_byte_operation_invariants; eauto.
  Qed.

  Lemma fin_inf_write_byte_spec :
    forall {addr_fin addr_inf ms_fin ms_fin' ms_inf byte_fin},
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      Memory64BitIntptr.MMEP.MemSpec.write_byte_spec ms_fin addr_fin byte_fin ms_fin' ->
      exists byte_inf ms_inf',
        MemoryBigIntptr.MMEP.MemSpec.write_byte_spec ms_inf addr_inf byte_inf ms_inf' /\
          sbyte_refine byte_inf byte_fin /\
          MemState_refine_prop ms_inf' ms_fin'.
  Proof.
    intros addr_fin addr_inf ms_fin ms_fin' ms_inf byte_fin MSR ADDR_CONV WBP.
    assert (Heap_in_bounds ms_fin') as HIB.
    { eapply write_byte_spec_MemPropT_Heap_in_bounds.
      apply MSR.
      apply WBP.
    }

    destruct WBP.

    pose proof (sbyte_refine_lifted byte_fin) as BYTE_REF.
    exists (lift_SByte byte_fin).
    pose proof fin_inf_set_byte_memory HIB MSR ADDR_CONV BYTE_REF byte_written as (ms_inf' & SET_INF & MSR').

    exists ms_inf'.
    split; auto.

    split; auto.
    - eapply fin_inf_write_byte_allowed; eauto.
    - eapply fin_inf_write_byte_operation_invariants; eauto.
      Unshelve.
       tauto.
  Qed.

  (* TODO: Move this *)
  Lemma get_consecutive_ptrs_0_is_nil :
    forall ms ms' ptr res,
      @InfMem.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs
        (MemPropT InfMem.MMEP.MMSP.MemState)
        (@MemPropT_Monad InfMem.MMEP.MMSP.MemState)
        (@MemPropT_RAISE_OOM InfMem.MMEP.MMSP.MemState)
        (@MemPropT_RAISE_ERROR InfMem.MMEP.MMSP.MemState)
        ptr 0 ms (success_unERR_UB_OOM (ms', res)) ->
      res = [].
  Proof.
    intros ms ms' ptr res GCP.
    Transparent InfMem.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs.
    unfold InfMem.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs in GCP.
    Opaque InfMem.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs.

    cbn in *.
    destruct GCP as (?&?&(?&?)&?&?&?&?); subst.
    cbn in *.
    destruct H1; subst.
    cbn in *.
    destruct H2; subst.
    auto.
  Qed.

  (* TODO: Move this *)
  Lemma map_monad_MemPropT_length :
    forall {S A B} {l} {f : A -> MemPropT S B} {s1 s2 res},
      @map_monad (MemPropT S) (@MemPropT_Monad S)
        A B f l s1 (success_unERR_UB_OOM (s2, res)) ->
      length res = length l.
  Proof.
    intros S A B l.
    induction l; intros f s1 s2 res HMAPM.
    cbn in *.
    destruct HMAPM; subst; auto.

    rewrite map_monad_unfold in HMAPM.
    cbn in HMAPM.
    destruct HMAPM as (?&?&?&?&?&?&?&?).
    subst.
    apply IHl in H0.
    cbn.
    auto.
  Qed.

  (* TODO: Move this *)
  Lemma zip_length :
    forall {A B C D} {x : list A} {y : list B} {z : list C} {w : list D},
      length x = length z ->
      length y = length w ->
      length (zip x y) = length (zip z w).
  Proof.
  Admitted.

  (* TODO: Move this *)
  Lemma zip_cons :
    forall {X Y} (x : X) xs (y : Y) ys,
      zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys.
  Proof.
    intros X Y x xs y ys.
    cbn.
    auto.
  Qed.

  (* TODO: Move this *)
  Lemma Forall2_zip :
    forall {X Y Z W} (xs : list X) (ys : list Y) (zs : list Z) (ws : list W) XY ZW,
      Forall2 XY xs ys ->
      Forall2 ZW zs ws ->
      Forall2 (fun '(x, z) '(y, w) => XY x y /\ ZW z w) (zip xs zs) (zip ys ws).
  Proof.
  Admitted.

  (* TODO: Move this *)
  Lemma sbytes_refine_length :
    forall bytes_inf bytes_fin,
      sbytes_refine bytes_inf bytes_fin ->
      length bytes_inf = length bytes_fin.
  Proof.
    intros bytes_inf bytes_fin H.
    red in H.
    eapply Util.Forall2_length; eauto.
  Qed.

  Lemma fin_inf_write_bytes_spec :
    forall a_fin a_inf ms_fin ms_fin' ms_inf bytes_inf bytes_fin res_fin,
      InfToFinAddrConvert.addr_convert a_inf = NoOom a_fin ->
      MemState_refine_prop ms_inf ms_fin ->
      sbytes_refine bytes_inf bytes_fin ->
      Memory64BitIntptr.MMEP.MemSpec.write_bytes_spec a_fin bytes_fin ms_fin (success_unERR_UB_OOM (ms_fin', res_fin)) ->
      exists res_inf ms_inf',
        MemoryBigIntptr.MMEP.MemSpec.write_bytes_spec a_inf bytes_inf ms_inf (success_unERR_UB_OOM (ms_inf', res_inf)) /\
          res_inf = res_fin /\
          MemState_refine_prop ms_inf' ms_fin'.
  Proof.
    intros a_fin a_inf ms_fin ms_fin' ms_inf bytes_inf bytes_fin res_fin ADDR_CONV MEM_REF1 BYTES_REF WRITE_SPEC.

    (* TODO: Make these opaque earlier *)
    Opaque Memory64BitIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs.
    Opaque MemoryBigIntptr.MMEP.MemSpec.MemHelpers.get_consecutive_ptrs.

    eapply MemPropT_fin_inf_bind.
    4: {
      apply WRITE_SPEC.
    }
    all: eauto.

    { (* MA *)
      intros a_fin0 ms_fin_ma H.
      eapply fin_inf_get_consecutive_ptrs_success_exists; eauto.
      erewrite sbytes_refine_length; eauto.
      apply H.
    }

    intros ms_inf0 ms_fin0 ms_fin'0 a_fin0 a_inf0 b_fin ADDRS MSR WRITES.
    eapply MemPropT_fin_inf_bind with
      (A_REF := Forall2 eq).
    4: apply WRITES.
    all: eauto.

    { (* MA *)
      intros a_fin1 ms_fin_ma MAP.
      eapply MemPropT_fin_inf_map_monad with
        (A_REF := (fun '(a_inf, byte_inf) '(a_fin, byte_fin) =>
                     InfToFinAddrConvert.addr_convert a_inf = NoOom a_fin /\
                       sbyte_refine byte_inf byte_fin)).
      4: apply MAP.
      all: eauto.

      { intros a_fin2 a_inf1 b_fin0 ms_fin1 ms_inf1 ms_fin_ma0 MSR' A_REF WRITE.
        destruct a_fin2, a_inf1.
        destruct A_REF.
        eapply fin_inf_write_byte_spec_MemPropT; eauto.
      }

      cbn in ADDRS.

      apply Forall2_zip; eauto.
      apply Forall2_flip in ADDRS.
      apply ADDRS.
    }

    intros ms_inf1 ms_fin1 ms_fin'1 a_fin1 a_inf1 b_fin0 H H0 H1.
    cbn.
    do 2 eexists; split; eauto.
    destruct b_fin0; split; auto.
    cbn in H1.
    destruct H1; subst; auto.
  Qed.

  (* TODO: Move this to somewhere it can
     be instantiated for all memory model
     instances
   *)
  Lemma read_bytes_spec_MemState_eq :
    forall a sz ms ms' res,
      Memory64BitIntptr.MMEP.MemSpec.read_bytes_spec a sz ms (ret (ms', res)) ->
      ms = ms'.
  Proof.
    intros a sz ms ms' res READ.
    red in READ.
    cbn in *.
    destruct READ as [sab [a0 [GCP HMAPM]]].
    apply Memory64BitIntptr.MMEP.get_consecutive_ptrs_MemPropT_MemState_eq in GCP. subst.
    generalize dependent res.
    induction a0; intros res HMAPM.
    - cbn in *.
      destruct HMAPM; subst; auto.
    - rewrite map_monad_unfold in HMAPM.
      cbn in *.
      destruct HMAPM as [sab0 [a' [[MS READ] HMAPM]]]; subst.
      destruct HMAPM as [sab [a'' [HMAPM [MS RES]]]]; subst.
      eapply IHa0.
      eapply HMAPM.
  Qed.

  Lemma handle_memcpy_fin_inf :
    forall {args args0 ms_fin ms_fin' ms_inf res_fin},
      Heap_in_bounds ms_fin' ->
      MemState_refine_prop ms_inf ms_fin ->
      Forall2 DVCInfFin.dvalue_refine_strict args0 args ->
      Memory64BitIntptr.MMEP.MemSpec.handle_memcpy_prop args ms_fin (ret (ms_fin', res_fin)) ->
      exists (res_inf : unit) (ms_inf' : MemoryBigIntptr.MMEP.MMSP.MemState),
        MemoryBigIntptr.MMEP.MemSpec.handle_memcpy_prop args0 ms_inf (ret (ms_inf', res_inf)) /\
          res_inf = res_fin /\
          MemState_refine_prop ms_inf' ms_fin'.
  Proof.
    intros args args0 ms_fin ms_fin' ms_inf res_fin MIB MSR ARGS HANDLER.

    (* Handler *)
    repeat (destruct ARGS;
            [solve [ inversion HANDLER
                   | red in HANDLER;
                     repeat break_match_hyp; inversion HANDLER
               ]
            |
           ]).
    red in HANDLER.
    repeat break_match_hyp; try inversion HANDLER; subst.
    { (* 32 bit memcpy *)
      inversion ARGS; subst.
      clear ARGS.
      rewrite DVCInfFin.dvalue_refine_strict_equation in H, H0, H1, H2, H3.

      apply dvalue_convert_strict_addr_inv in H as (a' & H & X); subst.
      apply dvalue_convert_strict_addr_inv in H0 as (a0' & H0 & X0); subst.
      apply dvalue_convert_strict_i32_inv in H1.
      apply dvalue_convert_strict_i32_inv in H2; subst.
      apply dvalue_convert_strict_i1_inv in H3; subst.

      unfold MemoryBigIntptr.MMEP.MemSpec.handle_memcpy_prop.
      unfold MemoryBigIntptr.MMEP.MemSpec.memcpy_spec.
      red in HANDLER.

      assert (LLVMParams64BitIntptr.Events.DV.unsigned x4 = LLVMParamsBigIntptr.Events.DV.unsigned x4) as X4.
      { reflexivity.
      }
      rewrite <- X4; clear X4.

      destruct res_fin.
      break_match_hyp.
      {
        exists tt. exists (lift_MemState ms_fin').
        split; auto.
        split; auto.
        apply lift_MemState_refine_prop.
        assumption.
      }

      erewrite <- fin_inf_no_overlap; eauto.
      repeat erewrite <- fin_inf_ptoi; eauto.
      break_match_goal.
      { eapply MemPropT_fin_inf_bind.
        4: apply HANDLER.
        all: eauto.

        { (* MA *)
          intros a_fin ms_fin_ma H1.
          eapply fin_inf_read_bytes_spec; eauto.
          apply H1.
        }

        intros ms_inf0 ms_fin0 ms_fin'0 a_fin a_inf b_fin BYTES MSR' WRITE.
        cbn in BYTES.
        eapply fin_inf_write_bytes_spec; eauto.
      }

      exists tt. exists (lift_MemState ms_fin').
      split; auto.
      split; auto.
      apply lift_MemState_refine_prop.
      assumption.
    }

    { (* 64 bit memcpy *)
      inversion ARGS; subst.
      clear ARGS.
      rewrite DVCInfFin.dvalue_refine_strict_equation in H, H0, H1, H2, H3.

      apply dvalue_convert_strict_addr_inv in H as (a' & H & X); subst.
      apply dvalue_convert_strict_addr_inv in H0 as (a0' & H0 & X0); subst.
      apply dvalue_convert_strict_i64_inv in H1.
      apply dvalue_convert_strict_i64_inv in H2; subst.
      apply dvalue_convert_strict_i1_inv in H3; subst.

      unfold MemoryBigIntptr.MMEP.MemSpec.handle_memcpy_prop.
      unfold MemoryBigIntptr.MMEP.MemSpec.memcpy_spec.
      red in HANDLER.

      assert (LLVMParams64BitIntptr.Events.DV.unsigned x4 = LLVMParamsBigIntptr.Events.DV.unsigned x4) as X4.
      { reflexivity.
      }
      rewrite <- X4; clear X4.

      destruct res_fin.
      break_match_hyp.
      {
        exists tt. exists (lift_MemState ms_fin').
        split; auto.
        split; auto.
        apply lift_MemState_refine_prop.
        assumption.
      }

      erewrite <- fin_inf_no_overlap; eauto.
      repeat erewrite <- fin_inf_ptoi; eauto.
      break_match_goal.
      { eapply MemPropT_fin_inf_bind.
        4: apply HANDLER.
        all: eauto.

        { (* MA *)
          intros a_fin ms_fin_ma H1.
          eapply fin_inf_read_bytes_spec; eauto.
          apply H1.
        }

        intros ms_inf0 ms_fin0 ms_fin'0 a_fin a_inf b_fin BYTES MSR' WRITE.
        cbn in BYTES.
        eapply fin_inf_write_bytes_spec; eauto.
      }

      exists tt. exists (lift_MemState ms_fin').
      split; auto.
      split; auto.
      apply lift_MemState_refine_prop.
      assumption.
    }

    { (* iptr memcpy *)
      inversion ARGS; subst.
      clear ARGS.
      rewrite DVCInfFin.dvalue_refine_strict_equation in H, H0, H1, H2, H3.

      apply dvalue_convert_strict_addr_inv in H as (a' & H & X); subst.
      apply dvalue_convert_strict_addr_inv in H0 as (a0' & H0 & X0); subst.
      apply dvalue_convert_strict_iptr_inv in H1 as (x4' & H1 & X4); subst.
      apply dvalue_convert_strict_iptr_inv in H2 as (x5' & H2 & X5); subst.
      apply dvalue_convert_strict_i1_inv in H3; subst.

      unfold MemoryBigIntptr.MMEP.MemSpec.handle_memcpy_prop.
      unfold MemoryBigIntptr.MMEP.MemSpec.memcpy_spec.
      red in HANDLER.

      assert (LLVMParams64BitIntptr.IP.to_Z x4 = LLVMParamsBigIntptr.IP.to_Z x4') as X4.
      { unfold LLVMParams64BitIntptr.IP.to_Z, LLVMParamsBigIntptr.IP.to_Z.
        unfold InterpreterStackBigIntptr.LP.IP.to_Z in *.
        erewrite IP.from_Z_to_Z; eauto.
      }
      rewrite <- X4; clear X4.

      destruct res_fin.
      break_match_hyp.
      {
        exists tt. exists (lift_MemState ms_fin').
        split; auto.
        split; auto.
        apply lift_MemState_refine_prop.
        assumption.
      }

      erewrite <- fin_inf_no_overlap; eauto.
      repeat erewrite <- fin_inf_ptoi; eauto.
      break_match_goal.
      { eapply MemPropT_fin_inf_bind.
        4: apply HANDLER.
        all: eauto.

        { (* MA *)
          intros a_fin ms_fin_ma H3.
          eapply fin_inf_read_bytes_spec; eauto.
          apply H3.
        }

        intros ms_inf0 ms_fin0 ms_fin'0 a_fin a_inf b_fin BYTES MSR' WRITE.
        cbn in BYTES.
        eapply fin_inf_write_bytes_spec; eauto.
      }

      exists tt. exists (lift_MemState ms_fin').
      split; auto.
      split; auto.
      apply lift_MemState_refine_prop.
      assumption.
    }
  Qed.




        (* TODO: Move this somewhere I can use it for both fin / inf *)
      #[global] Instance inf_frame_stack_preserved_symmetric :
        Symmetric InfMem.MMEP.MemSpec.frame_stack_preserved.
      Proof.
        intros x y FSP.
        red; red in FSP.
        intros fs. split; intros FS.
        apply FSP; auto.
        apply FSP; auto.
      Qed.

      (* TODO: Move this to where it can work for fin / inf *)
      Lemma frame_stack_eqv_snoc :
        forall fs1 fs2 f1 f2,
          MemoryBigIntptr.MMEP.MMSP.frame_stack_eqv fs1 fs2 ->
          MemoryBigIntptr.MMEP.MMSP.frame_eqv f1 f2 ->
          MemoryBigIntptr.MMEP.MMSP.frame_stack_eqv
            (InfMemMMSP.Snoc fs1 f1)
            (InfMemMMSP.Snoc fs2 f2).
      Proof.
        intros fs1 fs2 f1 f2 H H0.
        rewrite H.
        rewrite H0.
        reflexivity.
      Qed.


  (* TODO: Move this *)
  Lemma mem_push_spec_fin_inf :
    forall {m_fin_start m_fin_final m_inf_start m_inf_final},
      MemState_refine_prop m_inf_start m_fin_start ->
      MemState_refine_prop m_inf_final m_fin_final ->
      Memory64BitIntptr.MMEP.MemSpec.mempush_spec m_fin_start m_fin_final ->
      MemoryBigIntptr.MMEP.MemSpec.mempush_spec m_inf_start m_inf_final.
  Proof.
    intros m_fin_start m_fin_final m_inf_start m_inf_final MSR MSR' [FRESH INVARIANTS].

    split; cbn in *.
    - (* Fresh frame *)
      clear INVARIANTS.
      intros fs1 fs2 f MSFSP EMPTY PUSH.

      (* When I pop, I get a framestack that's equivalent to fs2... *)
      unfold MemoryBigIntptr.MMEP.MMSP.memory_stack_frame_stack_prop, Memory64BitIntptr.MMEP.MMSP.memory_stack_frame_stack_prop in *.
      cbn in *.

      apply MemState_refine_prop_frame_stack_preserved in MSR, MSR'.

      destruct PUSH.
      red in can_pop.
      destruct fs2; try contradiction.
      cbn in new_frame.

      rewrite <- new_frame.
      rewrite can_pop.
      rewrite <- MSFSP.

      pose proof InfMem.MMEP.empty_frame_eqv _ _ EMPTY MemoryBigIntptr.MMEP.empty_frame_nil as FNIL.
      rewrite FNIL.


      assert (Memory64BitIntptr.MMEP.MemSpec.push_frame_stack_spec
        (Memory64BitIntptr.MMEP.MMSP.memory_stack_frame_stack
           (Memory64BitIntptr.MMEP.MMSP.MemState_get_memory m_fin_start)) []
        (Memory64BitIntptr.MMEP.MMSP.Snoc
           (Memory64BitIntptr.MMEP.MMSP.memory_stack_frame_stack
              (Memory64BitIntptr.MMEP.MMSP.MemState_get_memory m_fin_start)) [])) as PUSH_FIN.
      { split; cbn; reflexivity.
      }

      specialize (FRESH
                    (Memory64BitIntptr.MMEP.MMSP.memory_stack_frame_stack
                       (Memory64BitIntptr.MMEP.MMSP.MemState_get_memory m_fin_start))
                    (Memory64BitIntptr.MMEP.MMSP.Snoc
                       (Memory64BitIntptr.MMEP.MMSP.memory_stack_frame_stack
                          (Memory64BitIntptr.MMEP.MMSP.MemState_get_memory m_fin_start)) [])
                    []
                 ).
      forward FRESH; try reflexivity.
      forward FRESH.
      apply Memory64BitIntptr.MMEP.empty_frame_nil.
      specialize (FRESH PUSH_FIN).

      apply FinMemMMSP.frame_stack_inv in FRESH.
      destruct FRESH as [FRESH | FRESH].
      2: {
        destruct FRESH as (?&?&?&?&?).
        discriminate.
      }

      destruct FRESH as (?&?&?&?&?&?&?&?).
      inv H0.

      destruct m_fin_final. destruct ms_memory_stack.
      cbn in *; subst.
      rewrite lift_FrameStack_snoc in MSR'.
      red in MSR'; cbn in MSR'.
      unfold InfMem.MMEP.MMSP.memory_stack_frame_stack_prop at 2 in MSR'.
      unfold InfMem.MMEP.MMSP.memory_stack_frame_stack in MSR'.

      red in MSR.
      pose proof MSFSP.
      apply MSR in H.


      destruct m_inf_final. destruct ms_memory_stack.
      specialize (MSR' memory_stack_frame_stack).
      cbn in *.
      destruct MSR' as [MSR1' MSR2'].
      unfold InfMem.MMEP.MMSP.memory_stack_frame_stack_prop in *.
      cbn in *.
      forward MSR1'.
      reflexivity.

      apply InfMem.MMEP.MMSP.frame_stack_inv in MSR1'.
      destruct MSR1' as [MSR1' | MSR1'].
      2: {
        destruct MSR1' as (?&?&?&?&?).
        discriminate.
      }

      destruct MSR1' as (?&?&?&?&?&?&?&?).
      inv H0.

      apply frame_eqv_empty_r in H2; subst.
      apply inf_frame_eqv_empty_r in FNIL; subst.
      apply inf_frame_eqv_empty_l in new_frame; subst.
      cbn in H5.
      apply inf_frame_eqv_empty_l in H5; subst.

      apply frame_stack_eqv_snoc.
      2: {
        cbn; reflexivity.
      }

      rewrite <- H4.
      apply frame_stack_eqv_lift in H1.
      rewrite H1.

      rewrite MSFSP.
      destruct m_fin_start. destruct ms_memory_stack.
      replace (Memory64BitIntptr.MMEP.MMSP.memory_stack_frame_stack
          (Memory64BitIntptr.MMEP.MMSP.MemState_get_memory
             {|
               FinMemMMSP.ms_memory_stack :=
                 {|
                   FinMemMMSP.memory_stack_memory := memory_stack_memory1;
                   FinMemMMSP.memory_stack_frame_stack := memory_stack_frame_stack;
                   FinMemMMSP.memory_stack_heap := memory_stack_heap1
                 |};
               FinMemMMSP.ms_provenance := ms_provenance1
             |})) with memory_stack_frame_stack by reflexivity.
      cbn in *.
      auto.
    - (* mempush_operation_invariants *)
      destruct INVARIANTS.
      split; cbn in *.
      + split; destruct mempush_op_reads.
        * eapply fin_inf_read_byte_allowed_all_preserved; eauto.
        * eapply fin_inf_read_byte_prop_all_preserved; eauto.
      + eapply fin_inf_write_byte_allowed_all_preserved; eauto.
      + eapply fin_inf_free_byte_allowed_all_preserved; eauto.
      + eapply fin_inf_allocations_preserved; eauto.
      + eapply fin_inf_preserve_allocation_ids; eauto.
      + eapply fin_inf_heap_preserved; eauto.
  Qed.

  (* TODO: Move this *)
  Lemma convert_Frame_cons_equation :
    forall {f a},
      convert_Frame (a :: f) =
        a' <- InfToFinAddrConvert.addr_convert a;;
        f' <- convert_Frame f;;
        NoOom (a' :: f').
  Proof.
    intros f a.
    induction f; cbn; auto.
  Qed.

  (* TODO: Move this *)
  Lemma fin_inf_ptr_in_frame_prop :
    forall {f_inf f_fin ptr_inf},
      InfMem.MMEP.MMSP.frame_eqv (lift_Frame f_fin) f_inf ->
      MemoryBigIntptr.MMEP.MMSP.ptr_in_frame_prop f_inf ptr_inf ->
      exists ptr_fin,
        InfToFinAddrConvert.addr_convert ptr_inf = NoOom ptr_fin /\
          Memory64BitIntptr.MMEP.MMSP.ptr_in_frame_prop f_fin ptr_fin.
  Proof.
    induction f_inf; intros f_fin ptr_inf F PTR.
    - cbn in *. contradiction.
    - cbn in F.
      red in F.
      apply F in PTR.
      red in PTR.
      apply in_map_iff in PTR as (?&?&?).
      apply in_map_iff in H0 as (?&?&?).
      subst.

      destruct x0.
      unfold fin_to_inf_addr in *.
      destruct (FinToInfAddrConvertSafe.addr_convert_succeeds (i, p)).
      apply FinToInfAddrConvertSafe.addr_convert_safe in e.
      destruct x.
      cbn in *.
      destruct ptr_inf; cbn in *; subst.
      pose proof int_to_ptr_succeeds_regardless_of_provenance e (pr2:=p1) as (?&?).
      exists x.
      split; auto.

      red.
      apply in_map_iff.
      exists (i, p). split; auto.
      erewrite ITOP.ptr_to_int_int_to_ptr; eauto.
      erewrite ITOP.ptr_to_int_int_to_ptr; eauto.
  Qed.

  (* TODO: Move this *)
  Lemma inf_fin_ptr_in_frame_prop :
    forall {f_inf f_fin ptr_fin},
      convert_Frame f_inf = NoOom f_fin ->
      Memory64BitIntptr.MMEP.MMSP.ptr_in_frame_prop f_fin ptr_fin ->
      exists ptr_inf,
        InfToFinAddrConvert.addr_convert ptr_inf = NoOom ptr_fin /\
          MemoryBigIntptr.MMEP.MMSP.ptr_in_frame_prop f_inf ptr_inf.
  Proof.
    induction f_inf; intros f_fin ptr_inf F PTR.
    - cbn in *.
      inv F.
      cbn in *.
      contradiction.
   - rewrite convert_Frame_cons_equation in F.
     cbn in F.
     break_match_hyp; inv F.
     break_match_hyp; inv H0.
     pose proof PTR as PTR'.
     red in PTR.
     cbn in PTR.
     destruct PTR.
     + destruct ptr_inf.
       destruct a.
       cbn in *; subst.
       destruct a0.
       unfold LLVMParams64BitIntptr.PTOI.ptr_to_int in H.
       cbn in *.
       exists (i0, p).
       cbn.
       split; auto.
       unfold FinITOP.int_to_ptr in *.
       break_match_hyp; inv Heqo.
       rewrite Int64.unsigned_repr in H.
       2: {
         apply Bool.orb_false_elim in Heqb.
         destruct Heqb.
         apply Z.ltb_nlt in H0.
         rewrite Z.geb_leb in H1.
         apply Z.leb_gt in H1.
         unfold Int64.max_unsigned.
         lia.
       }
       subst.

       rewrite Int64.repr_unsigned.
       auto.
     + specialize (IHf_inf f ptr_inf eq_refl).
       forward IHf_inf.
       {
         red. auto.
       }

       destruct IHf_inf as (?&?&?).
       exists x.
       split; auto.
       red.
       cbn.
       right.
       auto.
  Qed.

  (* TODO: Move this *)
  Lemma fin_inf_ptr_in_current_frame :
    forall {ms_inf ms_fin ptr_inf},
      MemState_refine_prop ms_inf ms_fin ->
      MemoryBigIntptr.MMEP.MemSpec.ptr_in_current_frame ms_inf ptr_inf ->
      exists ptr_fin,
        InfToFinAddrConvert.addr_convert ptr_inf = NoOom ptr_fin /\
          Memory64BitIntptr.MMEP.MemSpec.ptr_in_current_frame ms_fin ptr_fin.
  Proof.
    intros ms_inf ms_fin ptr_inf MSR PTR.
    destruct ms_inf as [[ms_inf fss_inf hs_inf] msprovs_inf].

    apply MemState_refine_prop_frame_stack_preserved in MSR.
    red in PTR.
    red in MSR.
    unfold InfMem.MMEP.MMSP.memory_stack_frame_stack_prop in *.
    cbn in *.
    specialize (MSR fss_inf).
    specialize (PTR fss_inf).
    destruct MSR as [MSR _].
    forward MSR; [reflexivity|].
    forward PTR; [reflexivity|].

    destruct fss_inf.
    { (* Single frame *)
      cbn in *.
      specialize (PTR f).
      forward PTR; [reflexivity|].

      destruct ms_fin as [[ms_fin fss_fin hs_fin] msprovs_fin].
      cbn in *.

      unfold Memory64BitIntptr.MMEP.MemSpec.ptr_in_current_frame, Memory64BitIntptr.MMEP.MMSP.memory_stack_frame_stack_prop.
      cbn.

      apply InfMem.MMEP.MMSP.frame_stack_inv in MSR.
      destruct MSR as [MSR | MSR].
      {
        destruct MSR as (?&?&?&?&?&?&?&?).
        discriminate.
      }

      destruct MSR as (?&?&?&?&?).
      inv H0.
      destruct fss_fin; inv H.
      rewrite <- H1 in PTR.

      eapply fin_inf_ptr_in_frame_prop in PTR; eauto.
      2: {
        reflexivity.
      }

      destruct PTR as (ptr_fin & CONV & PTR).
      exists ptr_fin.
      split; auto.

      intros fs H f0 H0.
      rewrite <- H in H0.
      cbn in H0.
      rewrite H0.
      auto.
    }

    { (* Multiple frames *)
      cbn in *.
      specialize (PTR f).
      forward PTR; [reflexivity|].

      destruct ms_fin as [[ms_fin fss_fin hs_fin] msprovs_fin].
      cbn in *.

      unfold Memory64BitIntptr.MMEP.MemSpec.ptr_in_current_frame, Memory64BitIntptr.MMEP.MMSP.memory_stack_frame_stack_prop.
      cbn.

      apply InfMem.MMEP.MMSP.frame_stack_inv in MSR.
      destruct MSR as [MSR | MSR].
      2: {
        destruct MSR as (?&?&?&?&?).
        discriminate.
      }

      destruct MSR as (?&?&?&?&?&?&?&?).
      inv H0.
      destruct fss_fin; inv H.
      rewrite <- H2 in PTR.

      eapply fin_inf_ptr_in_frame_prop in PTR; eauto.
      2: {
        reflexivity.
      }

      destruct PTR as (ptr_fin & CONV & PTR).
      exists ptr_fin.
      split; auto.

      intros fs H f0 H0.
      rewrite <- H in H0.
      cbn in H0.
      rewrite H0.
      auto.
    }
  Qed.

  (* TODO: Move this *)
  Lemma inf_fin_ptr_in_current_frame :
    forall {ms_inf ms_fin ptr_fin},
      MemState_refine_prop ms_inf ms_fin ->
      Memory64BitIntptr.MMEP.MemSpec.ptr_in_current_frame ms_fin ptr_fin ->
      exists ptr_inf,
        InfToFinAddrConvert.addr_convert ptr_inf = NoOom ptr_fin /\
          MemoryBigIntptr.MMEP.MemSpec.ptr_in_current_frame ms_inf ptr_inf.
  Proof.
    intros ms_inf ms_fin ptr_inf MSR PTR.
    destruct ms_inf as [[ms_inf fss_inf hs_inf] msprovs_inf].
    destruct ms_fin as [[ms_fin fss_fin hs_fin] msprovs_fin].

    apply MemState_refine_prop_frame_stack_preserved in MSR.
    red in PTR.
    red in MSR.
    unfold InfMem.MMEP.MMSP.memory_stack_frame_stack_prop in *.
    cbn in *.
    specialize (MSR fss_inf).
    specialize (PTR fss_fin).
    destruct MSR as [MSR _].
    forward MSR; [reflexivity|].
    forward PTR; [red; cbn; reflexivity|].

    destruct fss_fin.
    { (* Single frame *)
      cbn in *.
      specialize (PTR f).
      forward PTR; [reflexivity|].

      unfold MemoryBigIntptr.MMEP.MemSpec.ptr_in_current_frame, MemoryBigIntptr.MMEP.MMSP.memory_stack_frame_stack_prop.
      cbn.

      apply InfMem.MMEP.MMSP.frame_stack_inv in MSR.
      destruct MSR as [MSR | MSR].
      {
        destruct MSR as (?&?&?&?&?&?&?&?).
        discriminate.
      }

      destruct MSR as (?&?&?&?&?).
      inv H0.
      inv H.

      red in PTR.
      apply in_map_iff in PTR as (?&?&?).
      destruct ptr_inf.
      remember (fin_to_inf_addr x).
      destruct x.
      unfold LLVMParams64BitIntptr.PTOI.ptr_to_int in *.
      cbn in *.
      inv H.

      exists (Int64.unsigned i, p).
      split; auto.
      cbn.
      unfold FinITOP.int_to_ptr.
      break_match.
      {
        pose proof Integers.Int64.unsigned_range i.
        lia.
      }
      rewrite Int64.repr_unsigned.
      auto.

      intros fs H f0 H3.
      rewrite <- H in H3.
      cbn in H3.
      rewrite H3.
      rewrite <- H1.
      red. cbn.

      apply in_map_iff.
      exists (Int64.unsigned i, p0).
      split; auto.

      apply in_map_iff.
      exists (i0, p0).
      split; auto.
      unfold fin_to_inf_addr.
      break_match_goal.
      clear Heqs.
      apply FinToInfAddrConvertSafe.addr_convert_safe in e.
      destruct x.
      cbn in *.
      unfold FinITOP.int_to_ptr in *.
      break_match_hyp; inv e.
      rewrite Int64.unsigned_repr in H4.
      2: {
        unfold Int64.max_unsigned.
        lia.
      }

      subst.
      auto.
    }

    { (* Multiple frames *)
      specialize (PTR f).
      forward PTR; [cbn; reflexivity|].

      unfold MemoryBigIntptr.MMEP.MemSpec.ptr_in_current_frame, MemoryBigIntptr.MMEP.MMSP.memory_stack_frame_stack_prop.
      cbn.

      apply InfMem.MMEP.MMSP.frame_stack_inv in MSR.
      destruct MSR as [MSR | MSR].
      2: {
        destruct MSR as (?&?&?&?&?).
        discriminate.
      }

      destruct MSR as (?&?&?&?&?&?&?&?).
      inv H0.
      inv H.

      red in PTR.
      apply in_map_iff in PTR as (?&?&?).
      destruct ptr_inf.
      remember (fin_to_inf_addr x).
      destruct x.
      unfold LLVMParams64BitIntptr.PTOI.ptr_to_int in *.
      cbn in *.
      inv H.

      exists (Int64.unsigned i, p).
      split; auto.
      cbn.
      unfold FinITOP.int_to_ptr.
      break_match.
      {
        pose proof Integers.Int64.unsigned_range i.
        lia.
      }
      rewrite Int64.repr_unsigned.
      auto.

      intros fs H f0 H4.
      rewrite <- H in H4.
      cbn in H4.
      rewrite H4.
      rewrite <- H2.
      red. cbn.

      apply in_map_iff.
      exists (Int64.unsigned i, p0).
      split; auto.

      apply in_map_iff.
      exists (i0, p0).
      split; auto.
      unfold fin_to_inf_addr.
      break_match_goal.
      clear Heqs.
      apply FinToInfAddrConvertSafe.addr_convert_safe in e.
      destruct x.
      cbn in *.
      unfold FinITOP.int_to_ptr in *.
      break_match_hyp; inv e.
      rewrite Int64.unsigned_repr in H5.
      2: {
        unfold Int64.max_unsigned.
        lia.
      }

      subst.
      auto.
    }
  Qed.

  Lemma inf_fin_ptr_not_in_current_frame :
    forall {ms_inf ms_fin ptr_inf ptr_fin},
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert ptr_inf = NoOom ptr_fin ->
      ~ MemoryBigIntptr.MMEP.MemSpec.ptr_in_current_frame ms_inf ptr_inf ->
      ~ Memory64BitIntptr.MMEP.MemSpec.ptr_in_current_frame ms_fin ptr_fin.
  Proof.
    intros ms_inf ms_fin ptr_inf ptr_fin MSR ADDR_CONV PTR_NIN_FRAME PTR_IN_FRAME.
    eapply PTR_NIN_FRAME.
    eapply inf_fin_ptr_in_current_frame in PTR_IN_FRAME; eauto.
    destruct PTR_IN_FRAME as (?&?&?).
    pose proof InfToFinAddrConvert.addr_convert_injective _ _ _ ADDR_CONV H.
    subst.
    auto.
  Qed.

  (* TODO: Move this *)
  Lemma mem_pop_spec_fin_inf :
    forall {m_fin_start m_fin_final m_inf_start m_inf_final},
      MemState_refine_prop m_inf_start m_fin_start ->
      MemState_refine_prop m_inf_final m_fin_final ->
      Memory64BitIntptr.MMEP.MemSpec.mempop_spec m_fin_start m_fin_final ->
      MemoryBigIntptr.MMEP.MemSpec.mempop_spec m_inf_start m_inf_final.
  Proof.
    intros m_fin_start m_fin_final m_inf_start m_inf_final MSR1 MSR2 [BYTES_FREED NON_FRAME_BYTES_PRESERVED NON_FRAME_BYTES_READ POP_FRAME INVARIANTS].

    split.
    - (* Bytes freed *)
      clear NON_FRAME_BYTES_PRESERVED NON_FRAME_BYTES_READ POP_FRAME INVARIANTS.
      cbn in *.
      intros ptr PTR.

      (* ptr is in the current frame, which has a finite refinement,
         so there should be a finite version of ptr as well *)
      pose proof fin_inf_ptr_in_current_frame MSR1 PTR as (ptr_fin&PTR_CONV&PTR_FIN).
      eapply fin_inf_byte_not_allocated; eauto.
    - (* NON_FRAME_BYTES_PRESERVED *)
      clear - MSR1 MSR2 NON_FRAME_BYTES_PRESERVED.
      intros ptr aid PTR.

      destruct (InfToFinAddrConvert.addr_convert ptr) eqn:PTR_CONV.
      2: {
        pose proof inf_fin_big_address_byte_not_allocated MSR1 PTR_CONV.
        pose proof inf_fin_big_address_byte_not_allocated MSR2 PTR_CONV.
        split; intros.
        - exfalso. eapply H; eauto.
        - exfalso. eapply H0; eauto.
      }

      eapply inf_fin_ptr_not_in_current_frame in PTR; eauto.

      specialize (NON_FRAME_BYTES_PRESERVED a aid PTR).

      split; intros BYTE_ALLOCATED.
      + eapply inf_fin_byte_allocated in BYTE_ALLOCATED; eauto.
        apply NON_FRAME_BYTES_PRESERVED in BYTE_ALLOCATED.
        eapply fin_inf_byte_allocated; eauto.
      + eapply inf_fin_byte_allocated in BYTE_ALLOCATED; eauto.
        apply NON_FRAME_BYTES_PRESERVED in BYTE_ALLOCATED.
        eapply fin_inf_byte_allocated; eauto.
    - (* NON_FRAME_BYTES_READ *)
      clear - MSR1 MSR2 NON_FRAME_BYTES_READ.
      intros ptr byte PTR.

      destruct (InfToFinAddrConvert.addr_convert ptr) eqn:PTR_CONV.
      2: {
        pose proof inf_fin_big_address_byte_not_allocated MSR1 PTR_CONV.
        pose proof inf_fin_big_address_byte_not_allocated MSR2 PTR_CONV.
        split; intros.
        - exfalso.
          destruct H1.
          destruct read_byte_allowed_spec.
          destruct H1.
          eapply H; eauto.
        - exfalso.
          destruct H1.
          destruct read_byte_allowed_spec.
          destruct H1.
          eapply H0; eauto.
      }

      split; intros READ.
      + pose proof inf_fin_read_byte_spec MSR1 PTR_CONV READ as [byte_fin [READ_FIN BYTE_REF]].
        red in BYTE_REF.

        eapply inf_fin_ptr_not_in_current_frame in PTR; eauto.
        specialize (NON_FRAME_BYTES_READ a byte_fin PTR).
        eapply NON_FRAME_BYTES_READ in READ_FIN.
        eapply fin_inf_read_byte_spec; eauto.
      + pose proof inf_fin_read_byte_spec MSR2 PTR_CONV READ as [byte_fin [READ_FIN BYTE_REF]].
        red in BYTE_REF.

        eapply inf_fin_ptr_not_in_current_frame in PTR; eauto.
        specialize (NON_FRAME_BYTES_READ a byte_fin PTR).
        eapply NON_FRAME_BYTES_READ in READ_FIN.
        eapply fin_inf_read_byte_spec; eauto.
    - (* POP_FRAME *)
      clear - MSR1 MSR2 POP_FRAME.
      intros fs1 fs2 FSP POP.
      red; red in FSP.
      cbn in *.

      red in POP.
      destruct fs1; try contradiction.
      rewrite <- POP.

      destruct m_fin_start. destruct ms_memory_stack.
      destruct m_inf_start. destruct ms_memory_stack.
      cbn in *.
      destruct memory_stack_frame_stack0.
      apply MemoryBigIntptrInfiniteSpec.MMSP.frame_stack_eqv_sing_snoc_inv in FSP; contradiction.
      pose proof FSP as F.
      apply MemoryBigIntptrInfiniteSpec.MMSP.frame_stack_snoc_inv_fs in FSP.
      apply MemoryBigIntptrInfiniteSpec.MMSP.frame_stack_snoc_inv_f in F.

      rewrite <- FSP.
      apply MemState_refine_prop_frame_stack_preserved in MSR1, MSR2.
      cbn in *. red in MSR1, MSR2.
      cbn in MSR1, MSR2.
      unfold InfMem.MMEP.MMSP.memory_stack_frame_stack_prop in *.
      cbn in *.

      destruct m_inf_final. destruct ms_memory_stack.
      destruct m_fin_final. destruct ms_memory_stack.
      cbn in *.

      specialize (MSR2 memory_stack_frame_stack1).
      destruct MSR2 as [MSR2 _].
      forward MSR2; [reflexivity|].
      rewrite <- MSR2.

      specialize (MSR1 (InfMem.MMEP.MMSP.Snoc memory_stack_frame_stack0 f0)).
      destruct MSR1 as [MSR1 _].
      forward MSR1; [reflexivity|].

      destruct memory_stack_frame_stack.
      {
        cbn in MSR1.
        apply MemoryBigIntptrInfiniteSpec.MMSP.frame_stack_eqv_sing_snoc_inv in MSR1; contradiction.
      }
      rewrite lift_FrameStack_snoc in MSR1.
      apply MemoryBigIntptrInfiniteSpec.MMSP.frame_stack_snoc_inv_fs in MSR1.
      rewrite <- MSR1.

      unfold Memory64BitIntptr.MMEP.MMSP.memory_stack_frame_stack_prop in *.
      cbn in *.

      specialize (POP_FRAME (FinMem.MMEP.MMSP.Snoc memory_stack_frame_stack f1) memory_stack_frame_stack).
      forward POP_FRAME; [red; cbn; reflexivity|].
      forward POP_FRAME; [red; cbn; reflexivity|].
      red in POP_FRAME; cbn in POP_FRAME.
      eapply frame_stack_eqv_lift.
      auto.
    - (* mempop_operation_invariants *)
      destruct INVARIANTS.
      split; cbn in *.
      + eapply fin_inf_preserve_allocation_ids; eauto.
      + eapply fin_inf_heap_preserved; eauto.
  Qed.

  (* TODO: Move this *)
  Lemma dvalue_fin_to_inf_to_fin :
    forall d,
      DVCInfFin.dvalue_convert_strict (fin_to_inf_dvalue d) = NoOom d.
  Proof.
    intros d.
    pose proof fin_to_inf_dvalue_refine_strict d.
    auto.
  Qed.

  (* TODO: Move this *)
  Lemma uvalue_fin_to_inf_to_fin :
    forall u,
      DVCInfFin.uvalue_convert_strict (fin_to_inf_uvalue u) = NoOom u.
  Proof.
    intros u.
    pose proof fin_to_inf_uvalue_refine_strict u.
    auto.
  Qed.

  Set Nested Proofs Allowed.

  Lemma Heap_in_bounds_fresh_sid :
    forall ms_fin ms_fin' sid_fin,
      Heap_in_bounds ms_fin ->
      fresh_sid ms_fin (ret (ms_fin', sid_fin)) ->
      Heap_in_bounds ms_fin'.
  Proof.
    intros ms_fin ms_fin' sid_fin H H0.
    unfold fresh_sid in H0.
    cbn in H0.
    (* SAZ: It seems like we should add Heap_in_bounds_preserved in many places. *)
  Admitted.


  (* TODO: Factor out lemma about fresh_sid *)
  Lemma fresh_sid_fin_inf :
    forall (ms_inf : MemoryBigIntptr.MMEP.MMSP.MemState)
      (ms_fin ms_fin' : Memory64BitIntptr.MMEP.MMSP.MemState) (sid_fin : MemPropT.store_id),
      MemState_refine_prop ms_inf ms_fin ->
      fresh_sid ms_fin (ret (ms_fin', sid_fin)) ->
      exists sid_inf ms_inf',
        @fresh_sid (MemPropT MemoryBigIntptr.MMEP.MMSP.MemState) _  ms_inf (ret (ms_inf', sid_inf)) /\
          sid_inf = sid_fin /\
          MemState_refine_prop ms_inf' ms_fin'.
  Proof.
    intros ms_inf ms_fin ms_fin' sid_fin MSR FRESH.
    assert (Heap_in_bounds ms_fin') as HIB'.
    { eapply Heap_in_bounds_fresh_sid. 2 : { apply FRESH. }  apply MSR. }
    cbn in *.
    red in MSR.
    exists sid_fin.
    exists (lift_MemState ms_fin).
    cbn.
    destruct MSR as (?&?&?&?&?&?&?&?).
    destruct FRESH as (?&?&?&?&?&?&?&?).
    split.
    { split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]; auto.

      (* TODO: Move *)
      Lemma lift_SByte_sbyte_sid :
        forall byte sid,
          FinMem.MMEP.MMSP.MemByte.sbyte_sid byte = inr sid ->
          InfMem.MMEP.MMSP.MemByte.sbyte_sid (lift_SByte byte) = inr sid.
      Proof.
        intros byte sid H.
        unfold FinMem.MMEP.MMSP.MemByte.sbyte_sid in H.
        unfold InfMem.MMEP.MMSP.MemByte.sbyte_sid.

        (* Need to expose some things about sbyte_extractbypte / mkUbyte *)
      Admitted.

      (* TODO: separate into lemma? *)
      (* lift_MemState does not change which sids are used *)
      Lemma used_store_id_fin_inf :
        forall ms_inf ms_fin sid,
          MemState_refine_prop ms_inf ms_fin ->
          FinMem.MMEP.MemSpec.used_store_id_prop ms_fin sid <->
            InfMem.MMEP.MemSpec.used_store_id_prop ms_inf sid.
      Proof.
        intros ms_inf ms_fin sid MSR.
        split; intros USED.
        {
          cbn in *.
          red; red in USED.
          destruct USED as [ptr [byte [READ BYTE]]].

          pose proof FinToInfAddrConvertSafe.addr_convert_succeeds ptr as [ptr_inf CONV].
          pose proof FinToInfAddrConvertSafe.addr_convert_safe ptr ptr_inf CONV as CONV_INF.
          exists ptr_inf. exists (lift_SByte byte).
          split.
          - eapply fin_inf_read_byte_prop; eauto.
            apply sbyte_refine_lifted.
          - apply lift_SByte_sbyte_sid; auto.
        }
        {
          cbn in *.
          red; red in USED.
          destruct USED as [ptr [byte [READ BYTE]]].

          pose proof inf_fin_read_byte_prop_exists MSR READ as (ptr_fin&byte_fin&READ_FIN&BYTE_REFINE).
          exists ptr_fin. exists byte_fin.
          split; auto.

          unfold sbyte_refine, convert_SByte in BYTE_REFINE.
          break_match_hyp; cbn in BYTE_REFINE.
          break_match_hyp; inv BYTE_REFINE.
          break_match_hyp; inv H0.

          (* TODO: Need lemmas about sbyte_sid *)
          admit.
      Admitted.

      (* TODO: separate into lemma? *)
      (* lift_MemState does not change which sids are used *)
      Lemma used_store_id_lift_MemState :
        forall ms_fin sid,
          Heap_in_bounds ms_fin ->
          FinMem.MMEP.MemSpec.used_store_id_prop ms_fin sid <->
            InfMem.MMEP.MemSpec.used_store_id_prop (lift_MemState ms_fin) sid.
      Proof.
        intros ms_fin sid HIB.
        split; intros USED.
        {
          cbn in *.
          red; red in USED.
          destruct USED as [ptr [byte [READ BYTE]]].

          pose proof FinToInfAddrConvertSafe.addr_convert_succeeds ptr as [ptr_inf CONV].
          pose proof FinToInfAddrConvertSafe.addr_convert_safe ptr ptr_inf CONV as CONV_INF.
          exists ptr_inf. exists (lift_SByte byte).
          split.
          - eapply fin_inf_read_byte_prop; eauto.
            apply lift_MemState_refine_prop; auto.
            apply sbyte_refine_lifted.
          - destruct byte. cbn.
            unfold InfMem.MMEP.MMSP.MemByte.sbyte_sid.
            admit.
        }
        {
          cbn in *.
          red; red in USED.
          destruct USED as [ptr [byte [READ BYTE]]].

          pose proof (lift_MemState_refine_prop ms_fin HIB) as MSR.
          pose proof inf_fin_read_byte_prop_exists MSR READ as (ptr_fin&byte_fin&READ_FIN&BYTE_REFINE).
          exists ptr_fin. exists byte_fin.
          split; auto.

          unfold sbyte_refine, convert_SByte in BYTE_REFINE.
          break_match_hyp; cbn in BYTE_REFINE.
          break_match_hyp; inv BYTE_REFINE.
          break_match_hyp; inv H0.

          (* TODO: Need lemmas about sbyte_sid *)
          unfold FinMem.MMEP.MMSP.MemByte.sbyte_sid, InfMem.MMEP.MMSP.MemByte.sbyte_sid in *.
          break_match_hyp; inv BYTE.
          cbn in Hequ1.
          unfold FinMem.MP.BYTE_IMPL.sbyte_to_extractbyte.
          (* unfold Memory64BitIntptr.Byte.sbyte_to_extractbyte. *)
          admit.
      Admitted.

      intros USED.
      apply used_store_id_lift_MemState in USED.
      apply H7.

      (* TODO: Move this somewhere I can use it for both fin / inf *)
      Lemma used_store_id_read_byte_preserved_fin :
        forall ms1 ms2 sid,
          FinMem.MMEP.MemSpec.read_byte_preserved ms1 ms2 ->
          FinMem.MMEP.MemSpec.used_store_id_prop ms1 sid <-> FinMem.MMEP.MemSpec.used_store_id_prop ms2 sid.
      Proof.
        intros ms1 ms2 sid RBP.
        split; intros [addr [byte [RB SID]]].
        - red.
          exists addr. exists byte.
          split; auto.
          apply RBP. auto.
        - red.
          exists addr. exists byte.
          split; auto.
          apply RBP. auto.
      Qed.

      (* TODO: Move this somewhere I can use it for both fin / inf *)
      #[global] Instance fin_read_byte_allowed_all_preserved_symmetric :
        Symmetric FinMem.MMEP.MemSpec.read_byte_allowed_all_preserved.
      Proof.
        intros x y RBA.
        red; red in RBA.
        intros ptr. split; intros RA.
        apply RBA; auto.
        apply RBA; auto.
      Qed.

      (* TODO: Move this somewhere I can use it for both fin / inf *)
      #[global] Instance fin_read_byte_prop_all_preserved_symmetric :
        Symmetric FinMem.MMEP.MemSpec.read_byte_prop_all_preserved.
      Proof.
        red.
        intros x y RBP.
        red; red in RBP.
        intros ptr byte. split; intros RB.
        apply RBP; auto.
        apply RBP; auto.
      Qed.

      (* TODO: Move this somewhere I can use it for both fin / inf *)
      #[global] Instance fin_read_byte_preserved_symmetric :
        Symmetric FinMem.MMEP.MemSpec.read_byte_preserved.
      Proof.
        red.
        intros x y H.
        destruct H.
        red.
        split; symmetry; auto.
      Qed.

      eapply used_store_id_read_byte_preserved_fin; eauto.
      symmetry; auto.
      assumption.
    }
  Admitted.

  (* TODO: Move this, prove this *)
  Lemma fresh_provenance_fin_inf :
    forall (ms_inf : MemoryBigIntptr.MMEP.MMSP.MemState)
      (ms_fin ms_fin' : Memory64BitIntptr.MMEP.MMSP.MemState) (pr_fin : LLVMParamsBigIntptr.PROV.Provenance),
      MemState_refine_prop ms_inf ms_fin ->
      fresh_provenance ms_fin (ret (ms_fin', pr_fin)) ->
      exists pr_inf ms_inf',
        @fresh_provenance _ (MemPropT MemoryBigIntptr.MMEP.MMSP.MemState) _  ms_inf (ret (ms_inf', pr_inf)) /\
          pr_inf = pr_fin /\
          MemState_refine_prop ms_inf' ms_fin'.
  Proof.
  Admitted.

  (* TODO: Move this / put it somewhere I get it for fin / inf *)
  Lemma generate_num_undef_bytes_h_succ_inv :
    forall sz start_ix t sid bytes_fin,
      Memory64BitIntptr.MMEP.MemSpec.MemHelpers.generate_num_undef_bytes_h start_ix (N.succ sz) t sid = NoOom bytes_fin ->
      exists byte bytes_fin',
        Memory64BitIntptr.MMEP.MemSpec.MemHelpers.generate_num_undef_bytes_h (N.succ start_ix) sz t sid = NoOom bytes_fin' /\
          (x' <- IP.from_Z (Z.of_N start_ix);;
           ret (uvalue_sbyte (UVALUE_Undef t) t (UVALUE_IPTR x') sid)) = NoOom byte /\
          bytes_fin = byte :: bytes_fin'.
  Proof.
    induction sz using N.peano_rect; intros start_ix t sid bytes_fin GEN.
    unfold Memory64BitIntptr.MMEP.MemSpec.MemHelpers.generate_num_undef_bytes_h in *.
    - cbn in *.
      break_match_hyp; inv GEN.
      do 2 eexists.
      split; eauto.
    - unfold Memory64BitIntptr.MMEP.MemSpec.MemHelpers.generate_num_undef_bytes_h in GEN.

      pose proof @N.recursion_succ (N -> OOM (list SByte)) eq (fun _ : N => ret [])
        (fun (_ : N) (mf : N -> OOM (list SByte)) (x : N) =>
           rest_bytes <- mf (N.succ x);;
           x' <- IP.from_Z (Z.of_N x);;
           ret (uvalue_sbyte (UVALUE_Undef t) t (UVALUE_IPTR x') sid :: rest_bytes))
        eq_refl.
      forward H.
      { unfold Proper, respectful.
        intros x y H0 x0 y0 H1; subst.
        reflexivity.
      }
      specialize (H (N.succ sz)).
      rewrite H in GEN.
      clear H.

      cbn in *.
      break_match_hyp; inv GEN.
      break_match_hyp; inv H0.

      specialize (IHsz (N.succ start_ix) t sid l Heqo).
      destruct IHsz as (byte&bytes_fin'&GEN'&BYTE&BYTES).
      break_match_hyp; inv BYTE.

      eexists.
      eexists.
      split; eauto.
  Qed.

  (* TODO: Move this / put it somewhere I get it for fin / inf (get rid of this version) *)
  Lemma generate_num_undef_bytes_h_succ_inv_inf :
    forall sz start_ix t sid bytes_inf,
      MemoryBigIntptr.MMEP.MemSpec.MemHelpers.generate_num_undef_bytes_h start_ix (N.succ sz) t sid = NoOom bytes_inf ->
      exists byte bytes_inf',
        MemoryBigIntptr.MMEP.MemSpec.MemHelpers.generate_num_undef_bytes_h (N.succ start_ix) sz t sid = NoOom bytes_inf' /\
          (x' <- InfLP.IP.from_Z (Z.of_N start_ix);;
           ret (MemoryBigIntptr.Byte.uvalue_sbyte (LLVMParamsBigIntptr.Events.DV.UVALUE_Undef t) t (LLVMParamsBigIntptr.Events.DV.UVALUE_IPTR x') sid)) = NoOom byte /\
          bytes_inf = byte :: bytes_inf'.
  Proof.
    induction sz using N.peano_rect; intros start_ix t sid bytes_fin GEN.
    unfold Memory64BitIntptr.MMEP.MemSpec.MemHelpers.generate_num_undef_bytes_h in *.
    - cbn in *.
      inv GEN.
      do 2 eexists.
      split; eauto.
    - unfold Memory64BitIntptr.MMEP.MemSpec.MemHelpers.generate_num_undef_bytes_h in GEN.

      pose proof @N.recursion_succ (N -> OOM (list InfMem.MP.BYTE_IMPL.SByte)) eq (fun _ : N => ret [])
        (fun (_ : N) (mf : N -> OOM (list InfMem.MP.BYTE_IMPL.SByte)) (x : N) =>
           rest_bytes <- mf (N.succ x);;
           x' <- InfLP.IP.from_Z (Z.of_N x);;
           ret (MemoryBigIntptr.Byte.uvalue_sbyte (LLVMParamsBigIntptr.Events.DV.UVALUE_Undef t) t (LLVMParamsBigIntptr.Events.DV.UVALUE_IPTR x') sid :: rest_bytes))
        eq_refl.
      forward H.
      { unfold Proper, respectful.
        intros x y H0 x0 y0 H1; subst.
        reflexivity.
      }
      specialize (H (N.succ sz)).
      unfold MemoryBigIntptr.MMEP.MemSpec.MemHelpers.generate_num_undef_bytes_h in GEN.
      rewrite H in GEN.
      clear H.

      cbn in *.
      break_match_hyp; inv GEN.

      specialize (IHsz (N.succ start_ix) t sid l Heqo).
      destruct IHsz as (byte&bytes_fin'&GEN'&BYTE&BYTES).
      inv BYTE.

      eexists.
      eexists.
      split; eauto.
  Qed.

  (* TODO: Move this *)
  Lemma generate_num_undef_bytes_h_fin_inf :
    forall sz start_ix t sid bytes_fin,
      Memory64BitIntptr.MMEP.MemSpec.MemHelpers.generate_num_undef_bytes_h start_ix sz t sid = NoOom bytes_fin ->
      exists bytes_inf,
        MemoryBigIntptr.MMEP.MemSpec.MemHelpers.generate_num_undef_bytes_h start_ix sz t sid = NoOom bytes_inf /\
          sbytes_refine bytes_inf bytes_fin.
  Proof.
    induction sz using N.peano_ind; intros start_ix t sid bytes_fin GEN.
    - cbn in *. inv GEN.
      exists [].
      split; auto.
      red.
      auto.
    - cbn in GEN.
      pose proof GEN as GEN'.
      apply generate_num_undef_bytes_h_succ_inv in GEN'.
      destruct GEN' as (byte&bytes_fin'&GEN'&BYTE&BYTES).
      subst.
      cbn in *.
      break_match_hyp; inv BYTE.

      specialize (IHsz _ t sid bytes_fin' GEN') as (bytes_inf&GEN_INF&BYTES_REF).
      exists (MemoryBigIntptr.Byte.uvalue_sbyte (LLVMParamsBigIntptr.Events.DV.UVALUE_Undef t) t (LLVMParamsBigIntptr.Events.DV.UVALUE_IPTR (Z.of_N start_ix)) sid :: bytes_inf).
      split.
      + setoid_rewrite MemoryBigIntptrInfiniteSpecHelpers.generate_num_undef_bytes_h_cons.
        cbn.
        setoid_rewrite GEN_INF.
        reflexivity.
        eauto.
      + red.
        eapply Forall2_cons; eauto.
        red.
        unfold convert_SByte.
        break_match_goal.
        unfold MemoryBigIntptr.Byte.uvalue_sbyte in *.
        inv Heqs.
        cbn in *.
        repeat rewrite DVC1.uvalue_convert_strict_equation.
        cbn.
        unfold InterpreterStackBigIntptr.LP.IP.to_Z.
        rewrite Heqo.
        reflexivity.
  Qed.

  (* TODO: Move this *)
  Lemma generate_num_undef_bytes_fin_inf :
    forall sz t sid bytes_fin,
      Memory64BitIntptr.MMEP.MemSpec.MemHelpers.generate_num_undef_bytes sz t sid = NoOom bytes_fin ->
      exists bytes_inf,
        MemoryBigIntptr.MMEP.MemSpec.MemHelpers.generate_num_undef_bytes sz t sid = NoOom bytes_inf /\
          sbytes_refine bytes_inf bytes_fin.
  Proof.
    intros sz t sid bytes_fin H.
    eapply generate_num_undef_bytes_h_fin_inf; eauto.
  Qed.

  (* TODO: Move this *)
  Lemma generate_undef_bytes_fin_inf :
    forall {t sid bytes_fin},
      Memory64BitIntptr.MMEP.MemSpec.MemHelpers.generate_undef_bytes t sid = NoOom bytes_fin ->
      exists bytes_inf,
        MemoryBigIntptr.MMEP.MemSpec.MemHelpers.generate_undef_bytes t sid = NoOom bytes_inf /\
          sbytes_refine bytes_inf bytes_fin.
  Proof.
    intros t sid bytes_fin GEN.
    unfold Memory64BitIntptr.MMEP.MemSpec.MemHelpers.generate_undef_bytes in GEN.
    eapply generate_num_undef_bytes_fin_inf in GEN.
    eauto.
  Qed.

  (* TODO: Move to list utilities *)
  Lemma Forall2_repeatN :
    forall {X Y} (x : X) (y : Y) n (P : X -> Y -> Prop),
      P x y ->
      Forall2 P (repeatN n x) (repeatN n y).
  Proof.
    intros X Y x y n P H.
    induction n using N.peano_ind.
    - cbn; auto.
    - repeat rewrite repeatN_succ.
      constructor; auto.
  Qed.

  (* TODO: Move this *)
  Lemma Forall2_concat :
    forall {X Y} xs ys (P : X -> Y -> Prop),
      Forall2 (Forall2 P) xs ys ->
      Forall2 P (concat xs) (concat ys).
  Proof.
    intros X Y xs ys P ALL.
    induction ALL.
    - cbn; auto.
    - cbn.
      apply Forall2_app; auto.
  Qed.

  Lemma block_is_free_fin_inf :
    forall {ms_fin ms_inf addr_fin addrs_fin addr_inf addrs_inf len pr},
      MemState_refine_prop ms_inf ms_fin ->
      InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin ->
      Forall2 (fun addr_inf addr_fin => InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin) addrs_inf addrs_fin ->
      Memory64BitIntptr.MMEP.MemSpec.block_is_free ms_fin len pr addr_fin addrs_fin ->
      MemoryBigIntptr.MMEP.MemSpec.block_is_free ms_inf len pr addr_inf addrs_inf.
  Proof.
    intros ms_fin ms_inf addr_fin addrs_fin addr_inf addrs_inf len pr MSR ADDR_CONV ADDRS_CONV BLOCK_FREE.
    destruct BLOCK_FREE.
    split.
    - eapply fin_inf_get_consecutive_ptrs_success; eauto.
      eapply Forall2_flip.
      unfold Util.flip, flip.
      eauto.
      apply block_is_free_consecutive.
    - erewrite inf_fin_addr_convert_provenance; eauto.
      rewrite MemoryBigIntptrInfiniteSpec.LP.PROV.allocation_id_to_prov_provenance_to_allocation_id.
      rewrite PROV.allocation_id_to_prov_provenance_to_allocation_id in block_is_free_ptr_provenance.
      unfold MemoryBigIntptrInfiniteSpec.LP.PROV.provenance_to_prov.
      unfold PROV.provenance_to_prov in *.
      rewrite <- block_is_free_ptr_provenance.
      reflexivity.
    - intros ptr H.
      apply In_Nth in H. destruct H.
      eapply Util.Forall2_Nth_left in ADDRS_CONV; eauto.
      destruct ADDRS_CONV as (?&?&?).

      pose proof Util.Nth_In H0.

      specialize (block_is_free_ptrs_provenance _ H2).

      erewrite inf_fin_addr_convert_provenance; eauto.
      rewrite MemoryBigIntptrInfiniteSpec.LP.PROV.allocation_id_to_prov_provenance_to_allocation_id.
      rewrite PROV.allocation_id_to_prov_provenance_to_allocation_id in block_is_free_ptrs_provenance.
      unfold MemoryBigIntptrInfiniteSpec.LP.PROV.provenance_to_prov.
      unfold PROV.provenance_to_prov in *.
      rewrite <- block_is_free_ptrs_provenance.
      reflexivity.
    - intros ptr H.
      apply In_Nth in H. destruct H.
      eapply Util.Forall2_Nth_left in ADDRS_CONV; eauto.
      destruct ADDRS_CONV as (?&?&?).

      pose proof Util.Nth_In H0.

      specialize (block_is_free_bytes_are_free _ H2).

      eapply fin_inf_byte_not_allocated; eauto.
  Qed.

  Lemma find_free_block_fin_inf :
    forall {ms_fin_start ms_fin_final ms_inf_start len res_fin pr},
      MemState_refine_prop ms_inf_start ms_fin_start ->
      Memory64BitIntptr.MMEP.MemSpec.find_free_block len pr ms_fin_start (ret (ms_fin_final, res_fin)) ->
      exists res_inf ms_inf_final,
        MemoryBigIntptr.MMEP.MemSpec.find_free_block len pr ms_inf_start (ret (ms_inf_final, res_inf)) /\
          (fun '(addr_inf, addrs_inf) '(addr_fin, addrs_fin) =>
             InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin /\
               Forall2 (fun addr_inf addr_fin => InfToFinAddrConvert.addr_convert addr_inf = NoOom addr_fin) addrs_inf addrs_fin) res_inf res_fin /\
          MemState_refine_prop ms_inf_final ms_fin_final.
  Proof.
    intros ms_fin_start ms_fin_final ms_inf_start len [addr_fin addrs_fin] pr MSR FIND_FREE_BLOCK.


    pose proof FinToInfAddrConvertSafe.addr_convert_succeeds addr_fin as (addr_inf & CONV_FIN).
    apply FinToInfAddrConvertSafe.addr_convert_safe in CONV_FIN as CONV_INF.

    cbn in FIND_FREE_BLOCK.
    destruct FIND_FREE_BLOCK; subst.

    (* TODO: Move to listutils *)
    Lemma Forall2_map :
      forall {A B} (R : B -> B -> Prop) (f : A -> B) l1 l2,
        Forall2 (fun a b => R (f a) b) l1 l2 ->
        Forall2 R (map f l1) l2.
    Proof.
      intros A B R f l1 l2 ALL.
      induction ALL; cbn; auto.
    Qed.

    remember (map fin_to_inf_addr addrs_fin) as addrs_inf.
    assert (Forall2
              (fun (addr_inf0 : InfAddr.addr) (addr_fin0 : FinAddr.addr) =>
                 InfToFinAddrConvert.addr_convert addr_inf0 = NoOom addr_fin0) addrs_inf addrs_fin) as ADDRS.
    {
      clear H0; subst.
      induction addrs_fin; cbn; auto.

      apply Forall2_cons.
      { unfold fin_to_inf_addr.
        break_match_goal.
        clear Heqs.
        apply FinToInfAddrConvertSafe.addr_convert_safe in e.
        auto.
      }

      eapply IHaddrs_fin.
    }

    eapply @block_is_free_fin_inf with (addrs_inf:=map fin_to_inf_addr addrs_fin) in H0; eauto.
    2: {
      subst; apply ADDRS.
    }


    exists (addr_inf, addrs_inf).
    exists ms_inf_start.
    split.
    2: {
      split; auto.
    }

    red; cbn.
    split; subst; auto.
  Qed.

  Lemma addr_refine_fin_to_inf_addr :
    forall addr_fin,
      addr_refine (fin_to_inf_addr addr_fin) addr_fin.
  Proof.
    intros addr_fin.
    red. unfold fin_to_inf_addr.
    break_match_goal.
    clear Heqs.
    apply FinToInfAddrConvertSafe.addr_convert_safe in e.
    auto.
  Qed.

  (* TODO: Move this *)
  Lemma MemState_refine_prop_preserve_allocation_ids :
    forall ms_inf ms_fin,
      MemState_refine_prop ms_inf ms_fin ->
      InfMem.MMEP.MemSpec.preserve_allocation_ids ms_inf (lift_MemState ms_fin).
  Proof.
    intros ms_inf ms_fin MSR.
    destruct MSR.
    tauto.
  Qed.

  (* TODO: move this... Need to expose provenance_to_allocation_id to prove this *)
  Lemma provenance_to_allocation_id_fin_inf :
    forall pr,
      FinPROV.provenance_to_allocation_id pr = InfPROV.provenance_to_allocation_id pr.
  Proof.
  Admitted.

  Lemma extend_allocations_fin_inf :
    forall {ms_inf_start ms_fin_start ms_inf_final ms_fin_final addrs_fin addrs_inf pr},
      MemState_refine_prop ms_inf_start ms_fin_start ->
      MemState_refine_prop ms_inf_final ms_fin_final ->
      Forall2 addr_refine addrs_inf addrs_fin ->
      Memory64BitIntptr.MMEP.MemSpec.extend_allocations ms_fin_start addrs_fin pr ms_fin_final ->
      MemoryBigIntptr.MMEP.MemSpec.extend_allocations ms_inf_start addrs_inf pr ms_inf_final.
  Proof.
    intros ms_inf_start ms_fin_start ms_inf_final ms_fin_final addrs_fin addrs_inf pr MSR1 MSR2 ADDRS EXTEND.
    destruct EXTEND.

    split.
    - (* New bytes allocated *)
      intros ptr IN.
      apply In_Nth in IN as (i&IN).
      pose proof Util.Forall2_Nth_left IN ADDRS as (ptr_fin & NTH_FIN & REF).

      apply Util.Nth_In in NTH_FIN.
      rewrite provenance_to_allocation_id_fin_inf in extend_allocations_bytes_now_allocated.

      eapply fin_inf_byte_allocated; eauto.
    - (* Old allocations preserved *)
      intros ptr aid DISJOINT.
      split; intros ALLOC.
      { destruct (InfToFinAddrConvert.addr_convert ptr) eqn:CONV.
        { (* ptr in finite range *)
          specialize (extend_allocations_old_allocations_preserved a aid).
          forward extend_allocations_old_allocations_preserved.
          {
            intros p IN.
            apply In_Nth in IN as (i&IN).
            pose proof Util.Forall2_Nth_right IN ADDRS as (ptr_inf & NTH_INF & REF).

            eapply fin_inf_disjoint_ptr_byte; eauto.
            eapply DISJOINT.
            apply Util.Nth_In in NTH_INF.
            auto.
          }

          eapply fin_inf_byte_allocated; eauto.
          apply extend_allocations_old_allocations_preserved.
          eapply inf_fin_byte_allocated; eauto.
        }

        { (* Big pointer, shouldn't be allocated. *)
          exfalso.
          eapply inf_fin_big_address_byte_not_allocated.
          3: eauto.
          all: eauto.
        }
      }

      { destruct (InfToFinAddrConvert.addr_convert ptr) eqn:CONV.
        { (* ptr in finite range *)
          specialize (extend_allocations_old_allocations_preserved a aid).
          forward extend_allocations_old_allocations_preserved.
          {
            intros p IN.
            apply In_Nth in IN as (i&IN).
            pose proof Util.Forall2_Nth_right IN ADDRS as (ptr_inf & NTH_INF & REF).

            eapply fin_inf_disjoint_ptr_byte; eauto.
            eapply DISJOINT.
            apply Util.Nth_In in NTH_INF.
            auto.
          }

          eapply fin_inf_byte_allocated; eauto.
          apply extend_allocations_old_allocations_preserved.
          eapply inf_fin_byte_allocated; eauto.
        }

        { (* Big pointer, shouldn't be allocated. *)
          exfalso.
          eapply inf_fin_big_address_byte_not_allocated.
          3: eauto.
          all: eauto.
        }
      }
  Qed.

  Lemma extend_read_byte_allowed_fin_inf :
    forall {ms_inf_start ms_fin_start ms_inf_final ms_fin_final addrs_fin addrs_inf},
      MemState_refine_prop ms_inf_start ms_fin_start ->
      MemState_refine_prop ms_inf_final ms_fin_final ->
      Forall2 addr_refine addrs_inf addrs_fin ->
      Memory64BitIntptr.MMEP.MemSpec.extend_read_byte_allowed ms_fin_start addrs_fin ms_fin_final ->
      MemoryBigIntptr.MMEP.MemSpec.extend_read_byte_allowed ms_inf_start addrs_inf ms_inf_final.
  Proof.
    intros ms_inf_start ms_fin_start ms_inf_final ms_fin_final addrs_fin addrs_inf MSR1 MSR2 ADDRS EXTEND.
    destruct EXTEND.

    split.
    - (* New reads *)
      intros ptr IN.
      apply In_Nth in IN as (i&IN).
      pose proof Util.Forall2_Nth_left IN ADDRS as (ptr_fin & NTH_FIN & REF).

      apply Util.Nth_In in NTH_FIN.

      eapply fin_inf_read_byte_allowed; eauto.
    - (* Old reads preserved *)
      intros ptr DISJOINT.
      split; intros ALLOC.
      { destruct (InfToFinAddrConvert.addr_convert ptr) eqn:CONV.
        { (* ptr in finite range *)
          specialize (extend_read_byte_allowed_old_reads a).
          forward extend_read_byte_allowed_old_reads.
          {
            intros p IN.
            apply In_Nth in IN as (i&IN).
            pose proof Util.Forall2_Nth_right IN ADDRS as (ptr_inf & NTH_INF & REF).

            eapply fin_inf_disjoint_ptr_byte; eauto.
            eapply DISJOINT.
            apply Util.Nth_In in NTH_INF.
            auto.
          }

          eapply fin_inf_read_byte_allowed; eauto.
          apply extend_read_byte_allowed_old_reads.
          eapply inf_fin_read_byte_allowed; eauto.
        }

        { (* Big pointer, shouldn't be allocated. *)
          exfalso.
          destruct ALLOC as (?&?&?).
          eapply inf_fin_big_address_byte_not_allocated.
          3: eauto.
          all: eauto.
        }
      }

      { destruct (InfToFinAddrConvert.addr_convert ptr) eqn:CONV.
        { (* ptr in finite range *)
          specialize (extend_read_byte_allowed_old_reads a).
          forward extend_read_byte_allowed_old_reads.
          {
            intros p IN.
            apply In_Nth in IN as (i&IN).
            pose proof Util.Forall2_Nth_right IN ADDRS as (ptr_inf & NTH_INF & REF).

            eapply fin_inf_disjoint_ptr_byte; eauto.
            eapply DISJOINT.
            apply Util.Nth_In in NTH_INF.
            auto.
          }

          eapply fin_inf_read_byte_allowed; eauto.
          apply extend_read_byte_allowed_old_reads.
          eapply inf_fin_read_byte_allowed; eauto.
        }

        { (* Big pointer, shouldn't be allocated. *)
          exfalso.
          destruct ALLOC as (?&?&?).
          eapply inf_fin_big_address_byte_not_allocated.
          3: eauto.
          all: eauto.
        }
      }
  Qed.

  Lemma extend_reads_fin_inf :
    forall {ms_inf_start ms_fin_start ms_inf_final ms_fin_final addrs_fin addrs_inf bytes_inf bytes_fin},
      MemState_refine_prop ms_inf_start ms_fin_start ->
      MemState_refine_prop ms_inf_final ms_fin_final ->
      Forall2 addr_refine addrs_inf addrs_fin ->
      sbytes_refine bytes_inf bytes_fin ->
      Memory64BitIntptr.MMEP.MemSpec.extend_reads ms_fin_start addrs_fin bytes_fin ms_fin_final ->
      MemoryBigIntptr.MMEP.MemSpec.extend_reads ms_inf_start addrs_inf bytes_inf ms_inf_final.
  Proof.
    intros ms_inf_start ms_fin_start ms_inf_final ms_fin_final addrs_fin addrs_inf bytes_inf bytes_fin MSR1 MSR2 ADDRS BYTES EXTEND.
    destruct EXTEND.

    split.
    - (* New reads *)
      intros p ix byte NTH1 NTH2.
      pose proof Util.Forall2_Nth_left NTH1 ADDRS as (ptr_fin & NTH_FIN & REF_ADDR).
      pose proof Util.Forall2_Nth_left NTH2 BYTES as (byte_fin & NTH_FIN_BYTE & REF_BYTE).

      eapply fin_inf_read_byte_prop; eauto.
    - (* Old reads preserved *)
      intros ptr byte DISJOINT.
      split; intros READ.
      { (* ptr in finite range *)
        pose proof READ as READ'.
        eapply inf_fin_read_byte_prop_exists in READ' as (ptr_fin&byte_fin&READ'&ADDR_REF&BYTE_REF); eauto.
        specialize (extend_reads_old_reads ptr_fin byte_fin).
        forward extend_reads_old_reads.
        {
          intros p IN.
          apply In_Nth in IN as (i&IN).
          pose proof Util.Forall2_Nth_right IN ADDRS as (ptr_inf & NTH_INF & REF).

          eapply fin_inf_disjoint_ptr_byte; eauto.
          eapply DISJOINT.
          apply Util.Nth_In in NTH_INF.
          auto.
        }

        eapply fin_inf_read_byte_prop; eauto.
        apply extend_reads_old_reads.
        eapply inf_fin_read_byte_prop; eauto.
      }
      { (* ptr in finite range *)
        pose proof READ as READ'.
        eapply inf_fin_read_byte_prop_exists in READ' as (ptr_fin&byte_fin&READ'&ADDR_REF&BYTE_REF); eauto.
        specialize (extend_reads_old_reads ptr_fin byte_fin).
        forward extend_reads_old_reads.
        {
          intros p IN.
          apply In_Nth in IN as (i&IN).
          pose proof Util.Forall2_Nth_right IN ADDRS as (ptr_inf & NTH_INF & REF).

          eapply fin_inf_disjoint_ptr_byte; eauto.
          eapply DISJOINT.
          apply Util.Nth_In in NTH_INF.
          auto.
        }

        eapply fin_inf_read_byte_prop; eauto.
        apply extend_reads_old_reads.
        eapply inf_fin_read_byte_prop; eauto.
      }
  Qed.

  Lemma extend_write_byte_allowed_fin_inf :
    forall {ms_inf_start ms_fin_start ms_inf_final ms_fin_final addrs_fin addrs_inf},
      MemState_refine_prop ms_inf_start ms_fin_start ->
      MemState_refine_prop ms_inf_final ms_fin_final ->
      Forall2 addr_refine addrs_inf addrs_fin ->
      Memory64BitIntptr.MMEP.MemSpec.extend_write_byte_allowed ms_fin_start addrs_fin ms_fin_final ->
      MemoryBigIntptr.MMEP.MemSpec.extend_write_byte_allowed ms_inf_start addrs_inf ms_inf_final.
  Proof.
    intros ms_inf_start ms_fin_start ms_inf_final ms_fin_final addrs_fin addrs_inf MSR1 MSR2 ADDRS EXTEND.
    destruct EXTEND.

    split.
    - (* New writes *)
      intros ptr IN.
      apply In_Nth in IN as (i&IN).
      pose proof Util.Forall2_Nth_left IN ADDRS as (ptr_fin & NTH_FIN & REF).

      apply Util.Nth_In in NTH_FIN.

      eapply fin_inf_write_byte_allowed; eauto.
    - (* Old writes preserved *)
      intros ptr DISJOINT.
      split; intros ALLOC.
      { destruct (InfToFinAddrConvert.addr_convert ptr) eqn:CONV.
        { (* ptr in finite range *)
          specialize (extend_write_byte_allowed_old_writes a).
          forward extend_write_byte_allowed_old_writes.
          {
            intros p IN.
            apply In_Nth in IN as (i&IN).
            pose proof Util.Forall2_Nth_right IN ADDRS as (ptr_inf & NTH_INF & REF).

            eapply fin_inf_disjoint_ptr_byte; eauto.
            eapply DISJOINT.
            apply Util.Nth_In in NTH_INF.
            auto.
          }

          eapply fin_inf_write_byte_allowed; eauto.
          apply extend_write_byte_allowed_old_writes.
          eapply inf_fin_read_byte_allowed; eauto.
        }

        { (* Big pointer, shouldn't be allocated. *)
          exfalso.
          destruct ALLOC as (?&?&?).
          eapply inf_fin_big_address_byte_not_allocated.
          3: eauto.
          all: eauto.
        }
      }

      { destruct (InfToFinAddrConvert.addr_convert ptr) eqn:CONV.
        { (* ptr in finite range *)
          specialize (extend_write_byte_allowed_old_writes a).
          forward extend_write_byte_allowed_old_writes.
          {
            intros p IN.
            apply In_Nth in IN as (i&IN).
            pose proof Util.Forall2_Nth_right IN ADDRS as (ptr_inf & NTH_INF & REF).

            eapply fin_inf_disjoint_ptr_byte; eauto.
            eapply DISJOINT.
            apply Util.Nth_In in NTH_INF.
            auto.
          }

          eapply fin_inf_write_byte_allowed; eauto.
          apply extend_write_byte_allowed_old_writes.
          eapply inf_fin_read_byte_allowed; eauto.
        }

        { (* Big pointer, shouldn't be allocated. *)
          exfalso.
          destruct ALLOC as (?&?&?).
          eapply inf_fin_big_address_byte_not_allocated.
          3: eauto.
          all: eauto.
        }
      }
  Qed.

  Lemma extend_free_byte_allowed_fin_inf :
    forall {ms_inf_start ms_fin_start ms_inf_final ms_fin_final addrs_fin addrs_inf},
      MemState_refine_prop ms_inf_start ms_fin_start ->
      MemState_refine_prop ms_inf_final ms_fin_final ->
      Forall2 addr_refine addrs_inf addrs_fin ->
      Memory64BitIntptr.MMEP.MemSpec.extend_free_byte_allowed ms_fin_start addrs_fin ms_fin_final ->
      MemoryBigIntptr.MMEP.MemSpec.extend_free_byte_allowed ms_inf_start addrs_inf ms_inf_final.
  Proof.
    intros ms_inf_start ms_fin_start ms_inf_final ms_fin_final addrs_fin addrs_inf MSR1 MSR2 ADDRS EXTEND.
    destruct EXTEND.

    split.
    - (* New bytes *)
      intros ptr IN.
      apply In_Nth in IN as (i&IN).
      pose proof Util.Forall2_Nth_left IN ADDRS as (ptr_fin & NTH_FIN & REF).

      apply Util.Nth_In in NTH_FIN.

      eapply fin_inf_free_byte_allowed; eauto.
    - (* Old free bytes preserved *)
      intros ptr DISJOINT.
      split; intros ALLOC.
      { destruct (InfToFinAddrConvert.addr_convert ptr) eqn:CONV.
        { (* ptr in finite range *)
          specialize (extend_free_byte_allowed_old a).
          forward extend_free_byte_allowed_old.
          {
            intros p IN.
            apply In_Nth in IN as (i&IN).
            pose proof Util.Forall2_Nth_right IN ADDRS as (ptr_inf & NTH_INF & REF).

            eapply fin_inf_disjoint_ptr_byte; eauto.
            eapply DISJOINT.
            apply Util.Nth_In in NTH_INF.
            auto.
          }

          eapply fin_inf_free_byte_allowed; eauto.
          apply extend_free_byte_allowed_old.
          eapply inf_fin_read_byte_allowed; eauto.
        }

        { (* Big pointer, shouldn't be allocated. *)
          exfalso.
          destruct ALLOC as (?&?&?).
          eapply inf_fin_big_address_byte_not_allocated.
          3: eauto.
          all: eauto.
        }
      }

      { destruct (InfToFinAddrConvert.addr_convert ptr) eqn:CONV.
        { (* ptr in finite range *)
          specialize (extend_free_byte_allowed_old a).
          forward extend_free_byte_allowed_old.
          {
            intros p IN.
            apply In_Nth in IN as (i&IN).
            pose proof Util.Forall2_Nth_right IN ADDRS as (ptr_inf & NTH_INF & REF).

            eapply fin_inf_disjoint_ptr_byte; eauto.
            eapply DISJOINT.
            apply Util.Nth_In in NTH_INF.
            auto.
          }

          eapply fin_inf_free_byte_allowed; eauto.
          apply extend_free_byte_allowed_old.
          eapply inf_fin_read_byte_allowed; eauto.
        }

        { (* Big pointer, shouldn't be allocated. *)
          exfalso.
          destruct ALLOC as (?&?&?).
          eapply inf_fin_big_address_byte_not_allocated.
          3: eauto.
          all: eauto.
        }
      }
  Qed.

  Lemma extend_stack_frame_fin_inf :
    forall {ms_inf_start ms_fin_start ms_inf_final ms_fin_final addrs_fin addrs_inf},
      MemState_refine_prop ms_inf_start ms_fin_start ->
      MemState_refine_prop ms_inf_final ms_fin_final ->
      Forall2 addr_refine addrs_inf addrs_fin ->
      Memory64BitIntptr.MMEP.MemSpec.extend_stack_frame ms_fin_start addrs_fin ms_fin_final ->
      MemoryBigIntptr.MMEP.MemSpec.extend_stack_frame ms_inf_start addrs_inf ms_inf_final.
  Proof.
    intros ms_inf_start ms_fin_start ms_inf_final ms_fin_final addrs_fin addrs_inf MSR1 MSR2 ADDRS EXTEND.
    red in EXTEND.
    red.

    intros fs1 fs2 MSFSP ADD_PTRS.
    red.

    apply MemState_refine_prop_frame_stack_preserved in MSR1, MSR2.

    red in MSR1, MSR2.
    apply MSR1 in MSFSP.

    destruct ms_fin_start. destruct ms_memory_stack.
    destruct ms_inf_start. destruct ms_memory_stack.
    cbn in *.
    red in MSFSP.
    unfold InfMem.MMEP.MMSP.memory_stack_frame_stack_prop, Memory64BitIntptr.MMEP.MMSP.memory_stack_frame_stack_prop in *.
    cbn in *.

    generalize dependent addrs_fin.
    generalize dependent fs2.
    generalize dependent fs1.
    induction addrs_inf; intros fs1 MSFSP fs2 ADD_PTRS addrs_fin ADDRS EXTEND.
    - cbn in *.
      rewrite <- ADD_PTRS.
      inv ADDRS.
      cbn in *.

      rewrite <- MSFSP.
      apply MSR2.

      destruct ms_fin_final. destruct ms_memory_stack.
      cbn in *.

      apply frame_stack_eqv_lift.
      eapply EXTEND.
      reflexivity.
      reflexivity.
    - admit.

      (* cbn in *. *)
      (* inv ADDRS. *)
      (* destruct ADD_PTRS as (fs'&ADD1&ADD2). *)
      (* red in ADD2. *)
      (* eapply IHaddrs_inf; eauto. *)
      (* rewrite <- ADD_PTRS. *)
      (* inv ADDRS. *)
      (* cbn in *. *)
  Admitted.

  (* TODO: Not currently true, but will be once heap_preserved is modified *)
  Lemma heap_preserved_heap_in_bounds :
    forall {ms_fin_start ms_fin_final},
      Heap_in_bounds ms_fin_start ->
      Memory64BitIntptr.MMEP.MemSpec.heap_preserved ms_fin_start ms_fin_final ->
      Heap_in_bounds ms_fin_final.
  Proof.
  Admitted.

  Lemma MemState_refine_prop_heap_in_bounds :
    forall {ms_inf_start ms_fin_start},
      MemState_refine_prop ms_inf_start ms_fin_start ->
      Heap_in_bounds ms_fin_start.
  Proof.
    intros ms_inf_start ms_fin_start REF.
    destruct REF; tauto.
  Qed.

  Lemma allocate_bytes_post_conditions_fin_inf :
    forall {ms_fin_start ms_fin_final ms_inf_start t num_elements bytes_fin addr_fin addrs_fin bytes_inf pr},
      MemState_refine_prop ms_inf_start ms_fin_start ->
      (Forall2 sbyte_refine) bytes_inf bytes_fin ->
      Memory64BitIntptr.MMEP.MemSpec.allocate_bytes_post_conditions ms_fin_start t num_elements bytes_fin pr ms_fin_final addr_fin addrs_fin ->
      exists addr_inf addrs_inf ms_inf_final,
        MemoryBigIntptr.MMEP.MemSpec.allocate_bytes_post_conditions ms_inf_start t num_elements bytes_inf pr ms_inf_final addr_inf addrs_inf /\
          addr_refine addr_inf addr_fin /\
          Forall2 addr_refine addrs_inf addrs_fin /\
          MemState_refine_prop ms_inf_final ms_fin_final.
  Proof.
    intros ms_fin_start ms_fin_final ms_inf_start t num_elements bytes_fin addr_fin addrs_fin bytes_inf pr MSR BYTES ALLOC.
    destruct ALLOC.

    exists (fin_to_inf_addr addr_fin).
    exists (map fin_to_inf_addr addrs_fin).
    exists (lift_MemState ms_fin_final).

    assert (Forall2 addr_refine (map fin_to_inf_addr addrs_fin) addrs_fin) as ADDRS.
    {
      clear - addrs_fin.
      induction addrs_fin; cbn; auto.
      constructor; auto.
      apply addr_refine_fin_to_inf_addr.
    }

    assert (Heap_in_bounds ms_fin_final) as HIB_FINAL.
    {
      eapply heap_preserved_heap_in_bounds; eauto.
      eapply MemState_refine_prop_heap_in_bounds; eauto.
    }

    split.
    2: {
      split; [|split]; auto.
      - apply addr_refine_fin_to_inf_addr.
      - apply lift_MemState_refine_prop; auto.
    }

    split; intros; try reflexivity; try intuition.
    - eapply fin_inf_preserve_allocation_ids in H; eauto.
      apply lift_MemState_refine_prop; auto.
      red. symmetry. eapply allocate_bytes_provenances_preserved.
    - eapply fin_inf_preserve_allocation_ids in H; eauto.
      apply lift_MemState_refine_prop; auto.
    - eapply extend_allocations_fin_inf; eauto.
      apply lift_MemState_refine_prop; auto.
    - eapply extend_read_byte_allowed_fin_inf; eauto.
      apply lift_MemState_refine_prop; auto.
    - eapply extend_reads_fin_inf; eauto.
      apply lift_MemState_refine_prop; auto.
    - eapply extend_write_byte_allowed_fin_inf; eauto.
      apply lift_MemState_refine_prop; auto.
    - eapply extend_stack_frame_fin_inf; eauto.
      apply lift_MemState_refine_prop; auto.
    - eapply fin_inf_heap_preserved; eauto.
      apply lift_MemState_refine_prop; auto.
    - apply Util.Forall2_length in BYTES.
      lia.
  Qed.

  Lemma allocate_bytes_post_conditions_MemPropT_fin_inf :
    forall {ms_fin_start ms_fin_final ms_inf_start t num_elements bytes_fin addr_fin addrs_fin res_fin bytes_inf pr},
      MemState_refine_prop ms_inf_start ms_fin_start ->
      (Forall2 sbyte_refine) bytes_inf bytes_fin ->
      Memory64BitIntptr.MMEP.MemSpec.allocate_bytes_post_conditions_MemPropT t num_elements bytes_fin
        pr addr_fin addrs_fin ms_fin_start (ret (ms_fin_final, res_fin)) ->
      exists res_inf ms_inf_final,
        MemoryBigIntptr.MMEP.MemSpec.allocate_bytes_post_conditions_MemPropT t num_elements bytes_inf pr (fst res_inf) (snd res_inf) ms_inf_start (ret (ms_inf_final, res_inf)) /\
          (addr_refine × (Forall2 addr_refine)) res_inf res_fin /\
          MemState_refine_prop ms_inf_final ms_fin_final.
  Proof.
    intros ms_fin_start ms_fin_final ms_inf_start t num_elements bytes_fin addr_fin addrs_fin res_fin bytes_inf pr MSR BYTES ALLOC.
    repeat red in ALLOC.
    destruct res_fin.
    destruct ALLOC.
    destruct H0; subst.
    rename a into addr_fin.
    rename l into addrs_fin.

    eapply allocate_bytes_post_conditions_fin_inf in H; eauto.
    destruct H as (?&?&?&?&?&?&?).
    exists (x, x0). exists x1.
    split; auto.
    split; auto.
  Qed.


  Lemma allocate_bytes_with_pr_spec_MemPropT_fin_inf :
    forall {ms_fin_start ms_fin_final ms_inf_start t num_elements bytes_fin addr_fin bytes_inf pr},
      MemState_refine_prop ms_inf_start ms_fin_start ->
      (Forall2 sbyte_refine) bytes_inf bytes_fin ->
      Memory64BitIntptr.MMEP.MemSpec.allocate_bytes_with_pr_spec_MemPropT t num_elements bytes_fin pr ms_fin_start (ret (ms_fin_final, addr_fin)) ->
      exists addr_inf ms_inf_final,
        MemoryBigIntptr.MMEP.MemSpec.allocate_bytes_with_pr_spec_MemPropT t num_elements bytes_inf pr ms_inf_start (ret (ms_inf_final, addr_inf)) /\
          addr_refine addr_inf addr_fin /\
          MemState_refine_prop ms_inf_final ms_fin_final.
  Proof.
    intros ms_fin_start ms_fin_final ms_inf_start t num_elements bytes_fin addr_fin bytes_inf pr MSR BYTES ALLOC.
    assert (Heap_in_bounds ms_fin_start) as HIB.
    { apply MSR. }
    unfold MemoryBigIntptr.MMEP.MemSpec.allocate_bytes_with_pr_spec_MemPropT.
    eapply MemPropT_fin_inf_bind.
    4: {
      apply ALLOC.
    }
    all: eauto.

    { (* MA: find_free_block *)
      intros a_fin ms_fin_ma H.
      eapply find_free_block_fin_inf; eauto.
      eapply Util.Forall2_length in BYTES.
      rewrite BYTES.
      apply H.
    }

    (* K: allocate_bytes_post_conditions *)
    intros ms_inf ms_fin ms_fin' [addr_fin' addrs_fin] [addr_inf addrs_inf] b_fin [ADDR_CONV ADDRS_CONV] MSR' ALLOC_POST.

    eapply MemPropT_fin_inf_bind.
    4: apply ALLOC_POST.
    all: eauto.

    { (* allocate_bytes_post_conditions_MemPropT *)
      intros a_fin ms_fin_ma H.
      epose proof allocate_bytes_post_conditions_MemPropT_fin_inf MSR' BYTES H.
      destruct H0 as (?&?&?&?&?).
      cbn in *.
      exists x. exists x0.
      split; eauto.
      destruct x.
      cbn in *.
      destruct H0 as (?&?&?).
      assert (addr_inf = a).
      { destruct a_fin.
        destruct H1.
        cbn in fst_rel.
        red in fst_rel.
        destruct H as (?&?&?); subst.
        eapply InfToFinAddrConvert.addr_convert_injective; eauto.
      }
      assert (addrs_inf = l).
      { destruct a_fin.
        destruct H1.
        cbn in snd_rel.
        destruct H as (?&?&?); subst.
        clear - ADDRS_CONV snd_rel.
        generalize dependent l.
        induction ADDRS_CONV; intros l'' snd_rel.
        - inv snd_rel; auto.
        - inv snd_rel.
          erewrite IHADDRS_CONV; eauto.
          red in H3.
          assert (x=x0).
          eapply InfToFinAddrConvert.addr_convert_injective; eauto.
          subst.
          reflexivity.
      }
      subst.
      split; auto.
    }

    intros ms_inf0 ms_fin0 ms_fin'0 a_fin a_inf b_fin0 ADDRS_REF MSR'' H1.
    destruct H1; subst.
    do 2 eexists.
    split; cbn; eauto.
  Qed.

  Lemma allocate_bytes_spec_MemPropT_fin_inf :
    forall {ms_fin_start ms_fin_final ms_inf_start t num_elements bytes_fin addr_fin bytes_inf},
      MemState_refine_prop ms_inf_start ms_fin_start ->
      (Forall2 sbyte_refine) bytes_inf bytes_fin ->
      Memory64BitIntptr.MMEP.MemSpec.allocate_bytes_spec_MemPropT t num_elements
        bytes_fin ms_fin_start (ret (ms_fin_final, addr_fin)) ->
      exists addr_inf ms_inf_final,
        MemoryBigIntptr.MMEP.MemSpec.allocate_bytes_spec_MemPropT t num_elements
          bytes_inf ms_inf_start (ret (ms_inf_final, addr_inf)) /\
          addr_refine addr_inf addr_fin /\
          MemState_refine_prop ms_inf_final ms_fin_final.
  Proof.
    intros ms_fin_start ms_fin_final ms_inf_start t num_elements bytes_fin addr_fin bytes_inf MSR BYTES_REF ALLOCA_FIN.

    eapply MemPropT_fin_inf_bind.
    4: apply ALLOCA_FIN.
    all: eauto.

    { (* MA: fresh_provenance *)
      intros a_fin ms_fin_ma H.
      eapply fresh_provenance_fin_inf; eauto.
    }

    intros ms_inf ms_fin ms_fin' a_fin a_inf b_fin H H0 H1.
    cbn in H; subst.
    eapply allocate_bytes_with_pr_spec_MemPropT_fin_inf; eauto.
  Qed.

  Lemma allocate_dtyp_spec_fin_inf :
    forall {t num_elements ms_fin_start ms_fin_final ms_inf_start addr_fin},
      MemState_refine_prop ms_inf_start ms_fin_start ->
      Memory64BitIntptr.MMEP.MemSpec.allocate_dtyp_spec t num_elements ms_fin_start (ret (ms_fin_final, addr_fin)) ->
      exists addr_inf ms_inf_final,
        MemoryBigIntptr.MMEP.MemSpec.allocate_dtyp_spec t num_elements ms_inf_start (ret (ms_inf_final, addr_inf)) /\
          addr_refine addr_inf addr_fin /\
          MemState_refine_prop ms_inf_final ms_fin_final.
  Proof.
    intros t num_elements ms_fin_start ms_fin_final ms_inf_start addr_fin MSR ALLOCA.

    eapply MemPropT_fin_inf_bind.
    4: apply ALLOCA.
    all: eauto.

    { (* MA: fresh_sid *)
      intros a_fin ms_fin_ma FRESH_SID.
      eapply fresh_sid_fin_inf; eauto.
    }

    intros ms_inf_sid ms_fin_sid ms_fin' sid sid' b_fin SID MSR_SID K.
    cbn in SID; subst.

    eapply MemPropT_fin_inf_bind with (A_REF:=Forall2 sbytes_refine).
    4: apply K.
    all: eauto.

    { (* MA: generating undef bytes *)
      intros a_fin ms_fin_ma GEN_BYTE_BLOCKS.
      eapply MemPropT_fin_inf_map_monad with
        (B_REF:=sbytes_refine)
        (A_REF:=(fun (a_inf : MemPropT MemoryBigIntptr.MMEP.MMSP.MemState (list MemoryBigIntptr.MP.BYTE_IMPL.SByte)) (a_fin : MemPropT Memory64BitIntptr.MMEP.MMSP.MemState (list Memory64BitIntptr.MP.BYTE_IMPL.SByte)) =>
                   forall ms_inf ms_fin ms_fin' bytes_fin,
                     a_fin ms_fin (ret (ms_fin', bytes_fin)) ->
                     exists bytes_inf ms_inf',
                       a_inf ms_inf (ret (ms_inf', bytes_inf)) /\
                         sbytes_refine bytes_inf bytes_fin /\
                         ms_inf = ms_inf' /\
                         ms_fin = ms_fin')).
      4: apply GEN_BYTE_BLOCKS.
      all: eauto.

      {
        intros a_fin0 a_inf b_fin0 ms_fin ms_inf ms_fin_ma0 H H0 H1.
        unfold id in *.
        specialize (H0 ms_inf _ _ _ H1) as (?&?&?&?&?&?).
        subst.
        do 2 eexists.
        split; eauto.
      }

      apply Forall2_repeatN.
      intros ms_inf ms_fin ms_fin'0 bytes_fin H.
      red in H.
      break_match_hyp; inv H.
      rename l into bytes_fin.
      rename Heqo into GEN_FIN.
      apply generate_undef_bytes_fin_inf in GEN_FIN as (bytes_inf&GEN_INF&BYTES_REF).
      exists bytes_inf. exists ms_inf.
      split; auto.
      cbn. red.
      rewrite GEN_INF.
      cbn.
      auto.
    }

    intros ms_inf ms_fin ms_fin'0 a_fin a_inf b_fin0 BYTE_BLOCKS_REF MSR_GEN ALLOCA_BYTES.
    eapply allocate_bytes_spec_MemPropT_fin_inf; eauto.
    2: {
      apply ALLOCA_BYTES.
    }

    apply Forall2_concat; auto.
  Qed.

  (* TODO: Move this *)
  Lemma handle_alloca_fin_inf :
    forall {t num_elements align ms_fin_start ms_fin_final ms_inf_start d},
      MemState_refine_prop ms_inf_start ms_fin_start ->
      Memory64BitIntptr.MMEP.MemSpec.handle_memory_prop
        LLVMParams64BitIntptr.Events.DV.dvalue
        (LLVMParams64BitIntptr.Events.Alloca t num_elements align) ms_fin_start (ret (ms_fin_final, d)) ->
      exists d_inf ms_inf_final,
        MemoryBigIntptr.MMEP.MemSpec.handle_memory_prop DVCInfFin.DV1.dvalue
          (InterpreterStackBigIntptr.LP.Events.Alloca t num_elements align) ms_inf_start
          (ret (ms_inf_final, d_inf)) /\
          DVC1.dvalue_refine_strict d_inf d /\
          MemState_refine_prop ms_inf_final ms_fin_final.
  Proof.
    intros t num_elements align ms_fin_start ms_fin_final ms_inf_start d MSR HANDLE.

    eapply MemPropT_fin_inf_bind.
    4: apply HANDLE.
    all: eauto.

    { (* MA: allocate_dtyp_spec *)
      intros a_fin ms_fin_ma H.
      eapply allocate_dtyp_spec_fin_inf; eauto.
    }

    intros ms_inf ms_fin ms_fin' a_fin a_inf b_fin ADDR_REF MSR' H.
    cbn in H.
    destruct H; subst.
    cbn in ADDR_REF.

    cbn.
    do 2 eexists; split; eauto.
    split; auto.

    rewrite DVCInfFin.dvalue_refine_strict_equation.
    rewrite DVCInfFin.dvalue_convert_strict_equation.
    cbn.
    rewrite ADDR_REF.
    reflexivity.
  Qed.

  Lemma root_in_heap_prop_lifted_fin_inf :
    forall {h_fin ptr_inf ptr_fin},
      addr_refine ptr_inf ptr_fin ->
      Memory64BitIntptr.MMEP.MMSP.root_in_heap_prop h_fin ptr_fin ->
      MemoryBigIntptr.MMEP.MMSP.root_in_heap_prop (lift_Heap h_fin) ptr_inf.
  Proof.
    intros h_fin ptr_inf ptr_fin ADDR_REF ROOT.
    red; red in ROOT.
    unfold lift_Heap.
    rewrite IntMaps.IP.F.map_b.
    erewrite <- fin_inf_ptoi; eauto.
  Qed.

  Lemma root_in_heap_prop_lifted_fin_inf_transitive :
    forall {h_fin h_inf ptr_inf ptr_fin},
      InfMem.MMEP.MMSP.heap_eqv h_inf (lift_Heap h_fin) ->
      addr_refine ptr_inf ptr_fin ->
      Memory64BitIntptr.MMEP.MMSP.root_in_heap_prop h_fin ptr_fin ->
      MemoryBigIntptr.MMEP.MMSP.root_in_heap_prop h_inf ptr_inf.
  Proof.
    intros h_fin h_inf ptr_inf ptr_fin EQV ADDR_REF ROOT.
    rewrite EQV.
    eapply root_in_heap_prop_lifted_fin_inf; eauto.
  Qed.

  Lemma root_in_memstate_heap_fin_inf :
    forall {ms_inf ms_fin ptr_inf ptr_fin},
      MemState_refine_prop ms_inf ms_fin ->
      addr_refine ptr_inf ptr_fin ->
      Memory64BitIntptr.MMEP.MemSpec.root_in_memstate_heap ms_fin ptr_fin ->
      MemoryBigIntptr.MMEP.MemSpec.root_in_memstate_heap ms_inf ptr_inf.
  Proof.
    intros ms_inf ms_fin ptr_inf ptr_fin MSR ADDR_REF ROOT.
    destruct ms_inf; destruct ms_memory_stack.
    destruct ms_fin; destruct ms_memory_stack.
    apply MemState_refine_prop_heap_preserved in MSR.
    red; red in MSR; red in ROOT.
    cbn in *.
    unfold InfMem.MMEP.MMSP.memory_stack_heap_prop, Memory64BitIntptr.MMEP.MMSP.memory_stack_heap_prop in *; cbn in *.

    intros h H.
    eapply root_in_heap_prop_lifted_fin_inf_transitive; eauto.
    2: {
      eapply ROOT.
      reflexivity.
    }

    apply MSR in H.
    symmetry; auto.
  Qed.

  Lemma ptr_in_memstate_heap_fin_inf :
    forall {ms_inf ms_fin root_inf root_fin ptr_inf ptr_fin},
      MemState_refine_prop ms_inf ms_fin ->
      addr_refine root_inf root_fin ->
      addr_refine ptr_inf ptr_fin ->
      Memory64BitIntptr.MMEP.MemSpec.ptr_in_memstate_heap ms_fin root_fin ptr_fin ->
      MemoryBigIntptr.MMEP.MemSpec.ptr_in_memstate_heap ms_inf root_inf ptr_inf.
  Proof.
    intros ms_inf ms_fin root_inf root_fin ptr_inf ptr_fin MSR ROOT_REF PTR_REF IN_HEAP.
    destruct ms_inf; destruct ms_memory_stack.
    destruct ms_fin; destruct ms_memory_stack.
    apply MemState_refine_prop_heap_preserved in MSR.
    red; red in MSR; red in IN_HEAP.
    cbn in *.
    unfold InfMem.MMEP.MMSP.memory_stack_heap_prop, Memory64BitIntptr.MMEP.MMSP.memory_stack_heap_prop in *; cbn in *.

    intros h H.
    specialize (MSR memory_stack_heap).
    destruct MSR as [MSR _].
    forward MSR; [reflexivity|].
    rewrite <- MSR in H.
    rewrite <- H.

    replace root_inf with (fin_to_inf_addr root_fin).
    2: {
      unfold fin_to_inf_addr.
      break_match_goal.
      clear Heqs.
      apply FinToInfAddrConvertSafe.addr_convert_safe in e.
      eapply InfToFinAddrConvert.addr_convert_injective; eauto.
    }
    replace ptr_inf with (fin_to_inf_addr ptr_fin).
    2: {
      unfold fin_to_inf_addr.
      break_match_goal.
      clear Heqs.
      apply FinToInfAddrConvertSafe.addr_convert_safe in e.
      eapply InfToFinAddrConvert.addr_convert_injective; eauto.
    }

    apply ptr_in_heap_prop_lift.
    apply IN_HEAP.
    reflexivity.
  Qed.

  Lemma ptr_in_memstate_heap_inf_fin :
    forall {ms_inf ms_fin root_inf root_fin ptr_inf ptr_fin},
      MemState_refine_prop ms_inf ms_fin ->
      addr_refine root_inf root_fin ->
      addr_refine ptr_inf ptr_fin ->
      MemoryBigIntptr.MMEP.MemSpec.ptr_in_memstate_heap ms_inf root_inf ptr_inf ->
      Memory64BitIntptr.MMEP.MemSpec.ptr_in_memstate_heap ms_fin root_fin ptr_fin.
  Proof.
    intros ms_inf ms_fin root_inf root_fin ptr_inf ptr_fin MSR ROOT_REF PTR_REF IN_HEAP.
    destruct ms_inf; destruct ms_memory_stack.
    destruct ms_fin; destruct ms_memory_stack.
    apply MemState_refine_prop_heap_preserved in MSR.
    red; red in MSR; red in IN_HEAP.
    cbn in *.
    unfold InfMem.MMEP.MMSP.memory_stack_heap_prop, Memory64BitIntptr.MMEP.MMSP.memory_stack_heap_prop in *; cbn in *.

    intros h H.
    specialize (IN_HEAP memory_stack_heap).
    forward IN_HEAP; [reflexivity|].
    rewrite <- H.

    specialize (MSR memory_stack_heap).
    destruct MSR as [MSR _].
    forward MSR; [reflexivity|].
    rewrite <- MSR in IN_HEAP.

    pose proof ptr_in_heap_prop_lift_inv IN_HEAP ROOT_REF as (ptr_fin'&PTR_FIN_REF&IN_HEAP_FIN).
    rewrite PTR_REF in PTR_FIN_REF.
    inv PTR_FIN_REF.
    rename ptr_fin' into ptr_fin.
    eauto.
  Qed.

  Lemma ptr_in_memstate_heap_inf_fin_exists :
    forall {ms_inf ms_fin root_inf root_fin ptr_inf},
      MemState_refine_prop ms_inf ms_fin ->
      addr_refine root_inf root_fin ->
      MemoryBigIntptr.MMEP.MemSpec.ptr_in_memstate_heap ms_inf root_inf ptr_inf ->
      exists ptr_fin,
        addr_refine ptr_inf ptr_fin /\
        Memory64BitIntptr.MMEP.MemSpec.ptr_in_memstate_heap ms_fin root_fin ptr_fin.
  Proof.
    intros ms_inf ms_fin root_inf root_fin ptr_inf MSR ROOT_REF IN_HEAP.
    destruct ms_inf; destruct ms_memory_stack.
    destruct ms_fin; destruct ms_memory_stack.
    apply MemState_refine_prop_heap_preserved in MSR.
    red in MSR; red in IN_HEAP.
    cbn in *.
    unfold Memory64BitIntptr.MMEP.MemSpec.ptr_in_memstate_heap, InfMem.MMEP.MMSP.memory_stack_heap_prop, Memory64BitIntptr.MMEP.MMSP.memory_stack_heap_prop in *; cbn in *.

    specialize (MSR memory_stack_heap).
    destruct MSR as [MSR _].
    forward MSR; [reflexivity|].

    specialize (IN_HEAP (lift_Heap memory_stack_heap0)).
    forward IN_HEAP; [symmetry; auto|].

    (* TODO: Probably could split some of this into a separate lemma *)
    pose proof (ptr_in_heap_prop_lift_inv IN_HEAP ROOT_REF) as (?&?&?).
    exists x.
    split; auto.
    intros h H1.
    rewrite <- H1.
    apply H0.
  Qed.

  Lemma extend_heap_fin_inf :
    forall {ms_inf_start ms_fin_start ms_inf_final ms_fin_final addrs_fin addrs_inf},
      MemState_refine_prop ms_inf_start ms_fin_start ->
      MemState_refine_prop ms_inf_final ms_fin_final ->
      Forall2 addr_refine addrs_inf addrs_fin ->
      Memory64BitIntptr.MMEP.MemSpec.extend_heap ms_fin_start addrs_fin ms_fin_final ->
      MemoryBigIntptr.MMEP.MemSpec.extend_heap ms_inf_start addrs_inf ms_inf_final.
  Proof.
    intros ms_inf_start ms_fin_start ms_inf_final ms_fin_final addrs_fin addrs_inf MSR1 MSR2 ADDRS EXTEND.
    red in EXTEND.
    red.

    intros h1 h2 MSFSP ADD_PTRS.
    red.

    apply MemState_refine_prop_heap_preserved in MSR1, MSR2.

    red in MSR1, MSR2.
    apply MSR1 in MSFSP.

    destruct ms_fin_start. destruct ms_memory_stack.
    rename memory_stack_heap into h_fin_start.
    destruct ms_inf_start. destruct ms_memory_stack.
    rename memory_stack_heap into h_inf_start.
    destruct ms_fin_final. destruct ms_memory_stack.
    rename memory_stack_heap into h_fin_final.
    destruct ms_inf_final. destruct ms_memory_stack.
    rename memory_stack_heap into h_inf_final.
    cbn in *.

    red in MSFSP.
    unfold InfMem.MMEP.MMSP.memory_stack_heap_prop, Memory64BitIntptr.MMEP.MMSP.memory_stack_heap_prop in *.
    cbn in *.

    (* I think I need to be able to go from Inf.heap_eqv on lifted
       heaps to Fin.heap_eqv on non-lifted heaps in order to be able
       to use EXTEND...

       This may not hold right now because root_in_heap_prop only
       cares about
     *)
    apply MSR1 in MSFSP.
  Admitted.

  (* TODO: Not currently true, but will be once heap_preserved is modified *)
  Lemma extend_heap_heap_in_bounds :
    forall {ms_fin_start ms_fin_final ptrs_fin},
      Heap_in_bounds ms_fin_start ->
      Memory64BitIntptr.MMEP.MemSpec.extend_heap ms_fin_start ptrs_fin ms_fin_final ->
      Heap_in_bounds ms_fin_final.
  Proof.
  Admitted.

  Lemma malloc_bytes_post_conditions_fin_inf :
    forall {ms_fin_start ms_fin_final ms_inf_start bytes_fin addr_fin addrs_fin bytes_inf pr},
      MemState_refine_prop ms_inf_start ms_fin_start ->
      (Forall2 sbyte_refine) bytes_inf bytes_fin ->
      Memory64BitIntptr.MMEP.MemSpec.malloc_bytes_post_conditions ms_fin_start bytes_fin pr ms_fin_final addr_fin addrs_fin ->
      exists addr_inf addrs_inf ms_inf_final,
        MemoryBigIntptr.MMEP.MemSpec.malloc_bytes_post_conditions ms_inf_start bytes_inf pr ms_inf_final addr_inf addrs_inf /\
          addr_refine addr_inf addr_fin /\
          Forall2 addr_refine addrs_inf addrs_fin /\
          MemState_refine_prop ms_inf_final ms_fin_final.
  Proof.
    intros ms_fin_start ms_fin_final ms_inf_start bytes_fin addr_fin addrs_fin bytes_inf pr MSR BYTES ALLOC.
    destruct ALLOC.

    exists (fin_to_inf_addr addr_fin).
    exists (map fin_to_inf_addr addrs_fin).
    exists (lift_MemState ms_fin_final).

    assert (Forall2 addr_refine (map fin_to_inf_addr addrs_fin) addrs_fin) as ADDRS.
    {
      clear - addrs_fin.
      induction addrs_fin; cbn; auto.
      constructor; auto.
      apply addr_refine_fin_to_inf_addr.
    }

    assert (Heap_in_bounds ms_fin_final) as HIB_FINAL.
    {
      eapply extend_heap_heap_in_bounds; eauto.
      eapply MemState_refine_prop_heap_in_bounds; eauto.
    }

    split.
    2: {
      split; [|split]; auto.
      - apply addr_refine_fin_to_inf_addr.
      - apply lift_MemState_refine_prop; auto.
    }

    split; intros; try reflexivity; try intuition.
    - eapply fin_inf_preserve_allocation_ids in H; eauto.
      apply lift_MemState_refine_prop; auto.
      red. symmetry. eapply malloc_bytes_provenances_preserved.
    - eapply fin_inf_preserve_allocation_ids in H; eauto.
      apply lift_MemState_refine_prop; auto.
    - eapply extend_allocations_fin_inf; eauto.
      apply lift_MemState_refine_prop; auto.
    - eapply extend_read_byte_allowed_fin_inf; eauto.
      apply lift_MemState_refine_prop; auto.
    - eapply extend_reads_fin_inf; eauto.
      apply lift_MemState_refine_prop; auto.
    - eapply extend_write_byte_allowed_fin_inf; eauto.
      apply lift_MemState_refine_prop; auto.
    - eapply extend_free_byte_allowed_fin_inf; eauto.
      apply lift_MemState_refine_prop; auto.
    - eapply fin_inf_frame_stack_preserved; eauto.
      apply lift_MemState_refine_prop; auto.
    - eapply extend_heap_fin_inf; eauto.
      apply lift_MemState_refine_prop; auto.
  Qed.

  Lemma malloc_bytes_post_conditions_MemPropT_fin_inf :
    forall {ms_fin_start ms_fin_final ms_inf_start bytes_fin addr_fin addrs_fin res_fin bytes_inf pr},
      MemState_refine_prop ms_inf_start ms_fin_start ->
      (Forall2 sbyte_refine) bytes_inf bytes_fin ->
      Memory64BitIntptr.MMEP.MemSpec.malloc_bytes_post_conditions_MemPropT bytes_fin pr addr_fin addrs_fin ms_fin_start (ret (ms_fin_final, res_fin)) ->
      exists res_inf ms_inf_final,
        MemoryBigIntptr.MMEP.MemSpec.malloc_bytes_post_conditions_MemPropT bytes_inf pr (fst res_inf) (snd res_inf) ms_inf_start (ret (ms_inf_final, res_inf)) /\
          (addr_refine × (Forall2 addr_refine)) res_inf res_fin /\
          MemState_refine_prop ms_inf_final ms_fin_final.
  Proof.
    intros ms_fin_start ms_fin_final ms_inf_start bytes_fin addr_fin addrs_fin res_fin bytes_inf pr MSR BYTES ALLOC.
    repeat red in ALLOC.
    destruct res_fin.
    destruct ALLOC.
    destruct H0; subst.
    rename a into addr_fin.
    rename l into addrs_fin.

    eapply malloc_bytes_post_conditions_fin_inf in H; eauto.
    destruct H as (?&?&?&?&?&?&?).
    exists (x, x0). exists x1.
    split; auto.
    split; auto.
  Qed.

  (* TODO: Move this *)
  Lemma dvalue_refine_strict_i1_r_inv :
    forall v_inf x_fin,
      DVC1.dvalue_refine_strict v_inf (DVC1.DV2.DVALUE_I1 x_fin) ->
      exists x_inf,
        v_inf = DVC1.DV1.DVALUE_I1 x_inf /\
          LLVMParamsBigIntptr.Events.DV.unsigned x_inf = LLVMParams64BitIntptr.Events.DV.unsigned x_fin.
  Proof.
    intros v_inf x_fin REF.
    rewrite DVC1.dvalue_refine_strict_equation in REF.
    apply dvalue_convert_strict_i1_inv in REF.
    exists x_fin; tauto.
  Qed.

  (* TODO: Move this *)
  Lemma dvalue_refine_strict_i8_r_inv :
    forall v_inf x_fin,
      DVC1.dvalue_refine_strict v_inf (DVC1.DV2.DVALUE_I8 x_fin) ->
      exists x_inf,
        v_inf = DVC1.DV1.DVALUE_I8 x_inf /\
          LLVMParamsBigIntptr.Events.DV.unsigned x_inf = LLVMParams64BitIntptr.Events.DV.unsigned x_fin.
  Proof.
    intros v_inf x_fin REF.
    rewrite DVC1.dvalue_refine_strict_equation in REF.
    apply dvalue_convert_strict_i8_inv in REF.
    exists x_fin; tauto.
  Qed.

  (* TODO: Move this *)
  Lemma dvalue_refine_strict_i32_r_inv :
    forall v_inf x_fin,
      DVC1.dvalue_refine_strict v_inf (DVC1.DV2.DVALUE_I32 x_fin) ->
      exists x_inf,
        v_inf = DVC1.DV1.DVALUE_I32 x_inf /\
          LLVMParamsBigIntptr.Events.DV.unsigned x_inf = LLVMParams64BitIntptr.Events.DV.unsigned x_fin.
  Proof.
    intros v_inf x_fin REF.
    rewrite DVC1.dvalue_refine_strict_equation in REF.
    apply dvalue_convert_strict_i32_inv in REF.
    exists x_fin; tauto.
  Qed.

  (* TODO: Move this *)
  Lemma dvalue_refine_strict_i64_r_inv :
    forall v_inf x_fin,
      DVC1.dvalue_refine_strict v_inf (DVC1.DV2.DVALUE_I64 x_fin) ->
      exists x_inf,
        v_inf = DVC1.DV1.DVALUE_I64 x_inf /\
          LLVMParamsBigIntptr.Events.DV.unsigned x_inf = LLVMParams64BitIntptr.Events.DV.unsigned x_fin.
  Proof.
    intros v_inf x_fin REF.
    rewrite DVC1.dvalue_refine_strict_equation in REF.
    apply dvalue_convert_strict_i64_inv in REF.
    exists x_fin; tauto.
  Qed.

  (* TODO: Move this *)
  Lemma dvalue_refine_strict_iptr_r_inv :
    forall v_inf x_fin,
      DVC1.dvalue_refine_strict v_inf (DVC1.DV2.DVALUE_IPTR x_fin) ->
      exists x_inf,
        v_inf = DVC1.DV1.DVALUE_IPTR x_inf /\
          IP.from_Z (InterpreterStackBigIntptr.LP.IP.to_Z x_inf) = NoOom x_fin.
  Proof.
    intros v_inf x_fin REF.
    rewrite DVC1.dvalue_refine_strict_equation in REF.
    apply dvalue_convert_strict_iptr_inv in REF as (x&?&?).
    exists x; tauto.
  Qed.

  Lemma malloc_bytes_with_pr_spec_MemPropT_fin_inf :
    forall {ms_fin_start ms_fin_final ms_inf_start bytes_fin addr_fin bytes_inf pr},
      MemState_refine_prop ms_inf_start ms_fin_start ->
      (Forall2 sbyte_refine) bytes_inf bytes_fin ->
      Memory64BitIntptr.MMEP.MemSpec.malloc_bytes_with_pr_spec_MemPropT bytes_fin pr ms_fin_start (ret (ms_fin_final, addr_fin)) ->
      exists addr_inf ms_inf_final,
        MemoryBigIntptr.MMEP.MemSpec.malloc_bytes_with_pr_spec_MemPropT bytes_inf pr ms_inf_start (ret (ms_inf_final, addr_inf)) /\
          addr_refine addr_inf addr_fin /\
          MemState_refine_prop ms_inf_final ms_fin_final.
  Proof.
    intros ms_fin_start ms_fin_final ms_inf_start bytes_fin addr_fin bytes_inf pr MSR BYTES ALLOC.
    unfold MemoryBigIntptr.MMEP.MemSpec.malloc_bytes_with_pr_spec_MemPropT.
    eapply MemPropT_fin_inf_bind.
    4: apply ALLOC.
    all: eauto.

    { (* MA: find_free_block *)
      intros a_fin ms_fin_ma H.
      eapply find_free_block_fin_inf; eauto.
      eapply Util.Forall2_length in BYTES.
      rewrite BYTES.
      apply H.
    }

    (* K: malloc_bytes_post_conditions *)
    intros ms_inf ms_fin ms_fin' [addr_fin' addrs_fin] [addr_inf addrs_inf] b_fin [ADDR_CONV ADDRS_CONV] MSR' ALLOC_POST.

    eapply MemPropT_fin_inf_bind.
    4: apply ALLOC_POST.
    all: eauto.

    { (* allocate_bytes_post_conditions_MemPropT *)
      intros a_fin ms_fin_ma H.
      epose proof malloc_bytes_post_conditions_MemPropT_fin_inf MSR' BYTES H.
      destruct H0 as (?&?&?&?&?).
      cbn in *.
      exists x. exists x0.
      split; eauto.
      destruct x.
      cbn in *.
      destruct H0 as (?&?&?).
      assert (addr_inf = a).
      { destruct a_fin.
        destruct H1.
        cbn in fst_rel.
        red in fst_rel.
        destruct H as (?&?&?); subst.
        eapply InfToFinAddrConvert.addr_convert_injective; eauto.
      }
      assert (addrs_inf = l).
      { destruct a_fin.
        destruct H1.
        cbn in snd_rel.
        destruct H as (?&?&?); subst.
        clear - ADDRS_CONV snd_rel.
        generalize dependent l.
        induction ADDRS_CONV; intros l'' snd_rel.
        - inv snd_rel; auto.
        - inv snd_rel.
          erewrite IHADDRS_CONV; eauto.
          red in H3.
          assert (x=x0).
          eapply InfToFinAddrConvert.addr_convert_injective; eauto.
          subst.
          reflexivity.
      }
      subst.
      split; auto.
    }

    intros ms_inf0 ms_fin0 ms_fin'0 a_fin a_inf b_fin0 ADDRS_REF MSR'' H1.
    destruct H1; subst.
    do 2 eexists.
    split; cbn; eauto.
  Qed.

  Lemma handle_malloc_fin_inf :
    forall {ms_fin_start ms_fin_final ms_inf_start addr_fin args_fin args_inf},
      MemState_refine_prop ms_inf_start ms_fin_start ->
      Forall2 DVC1.dvalue_refine_strict args_inf args_fin ->
      Memory64BitIntptr.MMEP.MemSpec.handle_malloc_prop args_fin ms_fin_start (ret (ms_fin_final, addr_fin)) ->
      exists addr_inf ms_inf_final,
        MemoryBigIntptr.MMEP.MemSpec.handle_malloc_prop args_inf ms_inf_start (ret (ms_inf_final, addr_inf)) /\
          addr_refine addr_inf addr_fin /\
          MemState_refine_prop ms_inf_final ms_fin_final.
  Proof.
    intros ms_fin_start ms_fin_final ms_inf_start addr_fin args_fin args_inf MSR ARGS HANDLE.

    red in HANDLE.
    repeat (break_match_hyp; try contradiction).

    { (* I1 *)
      inv ARGS.
      inv H3.
      rename x0 into x_inf.
      rename x into x_fin.

      apply dvalue_refine_strict_i1_r_inv in H2 as (?&?&?); subst.

      eapply MemPropT_fin_inf_bind.
      4: apply HANDLE.
      all: eauto.

      { (* MA: fresh_sid *)
        intros a_fin ms_fin_ma FRESH.
        eapply fresh_sid_fin_inf; eauto.
      }

      intros ms_inf ms_fin ms_fin' a_fin a_inf b_fin SID MSR_SID HANDLE'.
      cbn in SID; subst.

      eapply MemPropT_fin_inf_bind.
      4: apply HANDLE'.
      all: eauto.

      { (* MA: generate_num_undef_bytes *)
        intros a_fin0 ms_fin_ma GEN.
        red in GEN.
        break_match_hyp; inv GEN.
        rename Heqo into GEN.
        eapply generate_num_undef_bytes_fin_inf in GEN as (bytes_inf&GEN&BYTES_REF).
        exists bytes_inf. exists ms_inf.
        split; eauto.
        red.
        rewrite H0.
        rewrite GEN.
        cbn.
        auto.
      }

      intros ms_inf0 ms_fin0 ms_fin'0 a_fin0 a_inf b_fin0 BYTES_REF MSR_GEN HANDLE''.
      eapply MemPropT_fin_inf_bind.
      4: apply HANDLE''.
      all: eauto.

      { (* MA: fresh_provenance *)
        intros a_fin1 ms_fin_ma FRESH_PR.
        eapply fresh_provenance_fin_inf; eauto.
      }

      intros ms_inf1 ms_fin1 ms_fin'1 a_fin1 a_inf0 b_fin1 PR MSR_PR HANDLE'''.
      cbn in PR; subst.
      eapply malloc_bytes_with_pr_spec_MemPropT_fin_inf; eauto.
    }

    { (* I8 *)
      inv ARGS.
      inv H3.
      rename x0 into x_inf.
      rename x into x_fin.

      apply dvalue_refine_strict_i8_r_inv in H2 as (?&?&?); subst.

      eapply MemPropT_fin_inf_bind.
      4: apply HANDLE.
      all: eauto.

      { (* MA: fresh_sid *)
        intros a_fin ms_fin_ma FRESH.
        eapply fresh_sid_fin_inf; eauto.
      }

      intros ms_inf ms_fin ms_fin' a_fin a_inf b_fin SID MSR_SID HANDLE'.
      cbn in SID; subst.

      eapply MemPropT_fin_inf_bind.
      4: apply HANDLE'.
      all: eauto.

      { (* MA: generate_num_undef_bytes *)
        intros a_fin0 ms_fin_ma GEN.
        red in GEN.
        break_match_hyp; inv GEN.
        rename Heqo into GEN.
        eapply generate_num_undef_bytes_fin_inf in GEN as (bytes_inf&GEN&BYTES_REF).
        exists bytes_inf. exists ms_inf.
        split; eauto.
        red.
        rewrite H0.
        rewrite GEN.
        cbn.
        auto.
      }

      intros ms_inf0 ms_fin0 ms_fin'0 a_fin0 a_inf b_fin0 BYTES_REF MSR_GEN HANDLE''.
      eapply MemPropT_fin_inf_bind.
      4: apply HANDLE''.
      all: eauto.

      { (* MA: fresh_provenance *)
        intros a_fin1 ms_fin_ma FRESH_PR.
        eapply fresh_provenance_fin_inf; eauto.
      }

      intros ms_inf1 ms_fin1 ms_fin'1 a_fin1 a_inf0 b_fin1 PR MSR_PR HANDLE'''.
      cbn in PR; subst.
      eapply malloc_bytes_with_pr_spec_MemPropT_fin_inf; eauto.
    }

    { (* I32 *)
      inv ARGS.
      inv H3.
      rename x0 into x_inf.
      rename x into x_fin.

      apply dvalue_refine_strict_i32_r_inv in H2 as (?&?&?); subst.

      eapply MemPropT_fin_inf_bind.
      4: apply HANDLE.
      all: eauto.

      { (* MA: fresh_sid *)
        intros a_fin ms_fin_ma FRESH.
        eapply fresh_sid_fin_inf; eauto.
      }

      intros ms_inf ms_fin ms_fin' a_fin a_inf b_fin SID MSR_SID HANDLE'.
      cbn in SID; subst.

      eapply MemPropT_fin_inf_bind.
      4: apply HANDLE'.
      all: eauto.

      { (* MA: generate_num_undef_bytes *)
        intros a_fin0 ms_fin_ma GEN.
        red in GEN.
        break_match_hyp; inv GEN.
        rename Heqo into GEN.
        eapply generate_num_undef_bytes_fin_inf in GEN as (bytes_inf&GEN&BYTES_REF).
        exists bytes_inf. exists ms_inf.
        split; eauto.
        red.
        rewrite H0.
        rewrite GEN.
        cbn.
        auto.
      }

      intros ms_inf0 ms_fin0 ms_fin'0 a_fin0 a_inf b_fin0 BYTES_REF MSR_GEN HANDLE''.
      eapply MemPropT_fin_inf_bind.
      4: apply HANDLE''.
      all: eauto.

      { (* MA: fresh_provenance *)
        intros a_fin1 ms_fin_ma FRESH_PR.
        eapply fresh_provenance_fin_inf; eauto.
      }

      intros ms_inf1 ms_fin1 ms_fin'1 a_fin1 a_inf0 b_fin1 PR MSR_PR HANDLE'''.
      cbn in PR; subst.
      eapply malloc_bytes_with_pr_spec_MemPropT_fin_inf; eauto.
    }

    { (* I64 *)
      inv ARGS.
      inv H3.
      rename x0 into x_inf.
      rename x into x_fin.

      apply dvalue_refine_strict_i64_r_inv in H2 as (?&?&?); subst.

      eapply MemPropT_fin_inf_bind.
      4: apply HANDLE.
      all: eauto.

      { (* MA: fresh_sid *)
        intros a_fin ms_fin_ma FRESH.
        eapply fresh_sid_fin_inf; eauto.
      }

      intros ms_inf ms_fin ms_fin' a_fin a_inf b_fin SID MSR_SID HANDLE'.
      cbn in SID; subst.

      eapply MemPropT_fin_inf_bind.
      4: apply HANDLE'.
      all: eauto.

      { (* MA: generate_num_undef_bytes *)
        intros a_fin0 ms_fin_ma GEN.
        red in GEN.
        break_match_hyp; inv GEN.
        rename Heqo into GEN.
        eapply generate_num_undef_bytes_fin_inf in GEN as (bytes_inf&GEN&BYTES_REF).
        exists bytes_inf. exists ms_inf.
        split; eauto.
        red.
        rewrite H0.
        rewrite GEN.
        cbn.
        auto.
      }

      intros ms_inf0 ms_fin0 ms_fin'0 a_fin0 a_inf b_fin0 BYTES_REF MSR_GEN HANDLE''.
      eapply MemPropT_fin_inf_bind.
      4: apply HANDLE''.
      all: eauto.

      { (* MA: fresh_provenance *)
        intros a_fin1 ms_fin_ma FRESH_PR.
        eapply fresh_provenance_fin_inf; eauto.
      }

      intros ms_inf1 ms_fin1 ms_fin'1 a_fin1 a_inf0 b_fin1 PR MSR_PR HANDLE'''.
      cbn in PR; subst.
      eapply malloc_bytes_with_pr_spec_MemPropT_fin_inf; eauto.
    }

    { (* IPTR *)
      inv ARGS.
      inv H3.
      rename x0 into x_inf.
      rename x into x_fin.

      apply dvalue_refine_strict_iptr_r_inv in H2 as (?&?&?); subst.

      eapply MemPropT_fin_inf_bind.
      4: apply HANDLE.
      all: eauto.

      { (* MA: fresh_sid *)
        intros a_fin ms_fin_ma FRESH.
        eapply fresh_sid_fin_inf; eauto.
      }

      intros ms_inf ms_fin ms_fin' a_fin a_inf b_fin SID MSR_SID HANDLE'.
      cbn in SID; subst.

      eapply MemPropT_fin_inf_bind.
      4: apply HANDLE'.
      all: eauto.

      { (* MA: generate_num_undef_bytes *)
        intros a_fin0 ms_fin_ma GEN.
        red in GEN.
        break_match_hyp; inv GEN.
        rename Heqo into GEN.
        eapply generate_num_undef_bytes_fin_inf in GEN as (bytes_inf&GEN&BYTES_REF).
        exists bytes_inf. exists ms_inf.
        split; eauto.
        red.
        rewrite <- InfLP.IP.to_Z_to_unsigned.
        rewrite <- FiniteIntptr.IP64Bit.to_Z_to_unsigned in GEN.
        erewrite fin_inf_from_Z_to_Z in GEN.
        3: apply H0.
        2: apply InfLP.IP.to_Z_from_Z.
        rewrite GEN.
        cbn.
        auto.
      }

      intros ms_inf0 ms_fin0 ms_fin'0 a_fin0 a_inf b_fin0 BYTES_REF MSR_GEN HANDLE''.
      eapply MemPropT_fin_inf_bind.
      4: apply HANDLE''.
      all: eauto.

      { (* MA: fresh_provenance *)
        intros a_fin1 ms_fin_ma FRESH_PR.
        eapply fresh_provenance_fin_inf; eauto.
      }

      intros ms_inf1 ms_fin1 ms_fin'1 a_fin1 a_inf0 b_fin1 PR MSR_PR HANDLE'''.
      cbn in PR; subst.
      eapply malloc_bytes_with_pr_spec_MemPropT_fin_inf; eauto.
    }
  Qed.

  Lemma dvalue_refine_strict_addr_r_inv:
  forall (v_inf : DVC1.DV1.dvalue) ptr_fin,
  DVC1.dvalue_refine_strict v_inf (DVC1.DV2.DVALUE_Addr ptr_fin) ->
  exists ptr_inf,
    v_inf = DVC1.DV1.DVALUE_Addr ptr_inf /\
      addr_refine ptr_inf ptr_fin.
  Proof.
    intros v_inf ptr_fin REF.
    rewrite DVC1.dvalue_refine_strict_equation in REF.
    apply dvalue_convert_strict_addr_inv in REF.
    destruct REF as (?&?&?).
    exists x; tauto.
  Qed.

  (* TODO: Move this *)
  Definition heap_refine h_inf h_fin : Prop :=
    InfMemMMSP.heap_eqv h_inf (lift_Heap h_fin).

  (* TODO: Finish this proof *)
  (* Will probably need to know heap is in finite range. *)
  Lemma free_block_prop_fin_inf :
    forall {h_fin_start h_fin_final h_inf_start h_inf_final ptr_fin ptr_inf},
      addr_refine ptr_inf ptr_fin ->
      heap_refine h_inf_start h_fin_start ->
      heap_refine h_inf_final h_fin_final ->
      Memory64BitIntptr.MMEP.MemSpec.free_block_prop h_fin_start ptr_fin h_fin_final ->
      MemoryBigIntptr.MMEP.MemSpec.free_block_prop h_inf_start ptr_inf h_inf_final.
  Proof.
    intros h_fin_start h_fin_final h_inf_start h_inf_final ptr_fin ptr_inf ADDR_REF HEAP_START_REF HEAP_FINAL_REF FREE_BLOCK.
    destruct FREE_BLOCK.
    split.
    - clear - ADDR_REF HEAP_START_REF HEAP_FINAL_REF free_block_ptrs_freed.
      intros ptr IN CONTRA.

      red in HEAP_FINAL_REF, HEAP_START_REF.
      rewrite HEAP_START_REF in IN.
      rewrite HEAP_FINAL_REF in CONTRA.

      eapply ptr_in_heap_prop_lift_inv in IN as (?&?&?); eauto.
      eapply ptr_in_heap_prop_lift_inv in CONTRA as (?&?&?); eauto.
      rewrite H in H1; inv H1.
      eapply free_block_ptrs_freed; eauto.
    - clear - ADDR_REF HEAP_START_REF HEAP_FINAL_REF free_block_root_freed.
      intros CONTRA.
      eapply free_block_root_freed.

      red in HEAP_FINAL_REF, HEAP_START_REF.
      rewrite HEAP_FINAL_REF in CONTRA.
      eapply root_in_heap_prop_lift_inv in CONTRA.
      destruct CONTRA as (?&?&?).
      rewrite ADDR_REF in H.
      inv H.
      eauto.
    - clear - ADDR_REF HEAP_START_REF HEAP_FINAL_REF free_block_disjoint_preserved.
      intros ptr root' DISJOINT.
      split; intros IN.
      {
        red in HEAP_FINAL_REF, HEAP_START_REF.
        rewrite HEAP_START_REF in IN.
        rewrite HEAP_FINAL_REF.

        assert (exists root_fin, fin_to_inf_addr root_fin = root') as (root_fin&ROOT_FIN).
        { (* TODO: Will need heap in bounds predicate *)
          admit.
        }
        subst.

        eapply ptr_in_heap_prop_lift_inv in IN as (?&?&?); eauto.
        2: {
          apply addr_refine_fin_to_inf_addr.
        }

        assert (fin_to_inf_addr x = ptr) as PTR_FIN.
        {
          unfold fin_to_inf_addr.
          break_match_goal.
          clear Heqs.
          apply FinToInfAddrConvertSafe.addr_convert_safe in e.
          eapply InfToFinAddrConvert.addr_convert_injective; eauto.
        }

        eapply fin_inf_disjoint_ptr_byte in DISJOINT; eauto.
        2: apply addr_refine_fin_to_inf_addr.

        subst.
        eapply ptr_in_heap_prop_lift.
        specialize (free_block_disjoint_preserved x root_fin DISJOINT).
        destruct free_block_disjoint_preserved.
        apply H1.
        auto.
      }

      {
        red in HEAP_FINAL_REF, HEAP_START_REF.
        rewrite HEAP_FINAL_REF in IN.
        rewrite HEAP_START_REF.

        assert (exists root_fin, fin_to_inf_addr root_fin = root') as (root_fin&ROOT_FIN).
        { (* TODO: Will need heap in bounds predicate *)
          admit.
        }
        subst.

        eapply ptr_in_heap_prop_lift_inv in IN as (?&?&?); eauto.
        2: {
          apply addr_refine_fin_to_inf_addr.
        }

        assert (fin_to_inf_addr x = ptr) as PTR_FIN.
        {
          unfold fin_to_inf_addr.
          break_match_goal.
          clear Heqs.
          apply FinToInfAddrConvertSafe.addr_convert_safe in e.
          eapply InfToFinAddrConvert.addr_convert_injective; eauto.
        }

        eapply fin_inf_disjoint_ptr_byte in DISJOINT; eauto.
        2: apply addr_refine_fin_to_inf_addr.

        subst.
        eapply ptr_in_heap_prop_lift.
        specialize (free_block_disjoint_preserved x root_fin DISJOINT).
        destruct free_block_disjoint_preserved.
        apply H2.
        auto.
      }
    - clear - ADDR_REF HEAP_START_REF HEAP_FINAL_REF free_block_disjoint_roots.
      intros root' DISJOINT.

      split; intros IN.
      {
        red in HEAP_FINAL_REF, HEAP_START_REF.
        rewrite HEAP_START_REF in IN.
        rewrite HEAP_FINAL_REF.

        assert (exists root_fin, fin_to_inf_addr root_fin = root') as (root_fin&ROOT_FIN).
        { (* TODO: Will need heap in bounds predicate *)
          admit.
        }
        subst.

        eapply root_in_heap_prop_lifted_fin_inf.
        apply addr_refine_fin_to_inf_addr.

        eapply root_in_heap_prop_lift_inv in IN as (?&?&?).
        assert (x = root_fin).
        { apply fin_to_inf_addr_conv_inf in H.
          unfold fin_to_inf_addr in H.
          break_match_hyp.
          break_match_hyp.
          subst.
          clear Heqs Heqs0.
          eapply FinToInfAddrConvert.addr_convert_injective; eauto.
        }

        eapply fin_inf_disjoint_ptr_byte in DISJOINT; eauto.

        subst.
        specialize (free_block_disjoint_roots root_fin DISJOINT).
        destruct free_block_disjoint_roots.
        auto.
      }

      {
        red in HEAP_FINAL_REF, HEAP_START_REF.
        rewrite HEAP_FINAL_REF in IN.
        rewrite HEAP_START_REF.

        assert (exists root_fin, fin_to_inf_addr root_fin = root') as (root_fin&ROOT_FIN).
        { (* TODO: Will need heap in bounds predicate *)
          admit.
        }
        subst.

        eapply root_in_heap_prop_lifted_fin_inf.
        apply addr_refine_fin_to_inf_addr.

        eapply root_in_heap_prop_lift_inv in IN as (?&?&?).
        assert (x = root_fin).
        { apply fin_to_inf_addr_conv_inf in H.
          unfold fin_to_inf_addr in H.
          break_match_hyp.
          break_match_hyp.
          subst.
          clear Heqs Heqs0.
          eapply FinToInfAddrConvert.addr_convert_injective; eauto.
        }

        eapply fin_inf_disjoint_ptr_byte in DISJOINT; eauto.

        subst.
        specialize (free_block_disjoint_roots root_fin DISJOINT).
        destruct free_block_disjoint_roots.
        auto.
      }
  Admitted.

  Lemma handle_free_spec_fin_inf :
    forall {ms_fin_start ms_fin_final ms_inf_start ptr_fin ptr_inf},
      MemState_refine_prop ms_inf_start ms_fin_start ->
      addr_refine ptr_inf ptr_fin ->
      Memory64BitIntptr.MMEP.MemSpec.free_spec ms_fin_start ptr_fin ms_fin_final ->
      exists (ms_inf_final : MemoryBigIntptr.MMEP.MMSP.MemState),
        MemoryBigIntptr.MMEP.MemSpec.free_spec ms_inf_start ptr_inf ms_inf_final /\
          MemState_refine_prop ms_inf_final ms_fin_final.
  Proof.
    intros ms_fin_start ms_fin_final ms_inf_start ptr_fin ptr_inf MSR PTR_REF FREE.
    destruct FREE.

    exists (lift_MemState ms_fin_final).

    split.
    2: apply lift_MemState_refine_prop.

    split.
    - eapply root_in_memstate_heap_fin_inf; eauto.
    - destruct free_was_allocated.
      eapply fin_inf_byte_allocated in H; eauto.
    - intros ptr H.
      { destruct (InfToFinAddrConvert.addr_convert ptr) eqn:CONV.
        { (* ptr in finite range *)
          eapply ptr_in_memstate_heap_inf_fin in H; eauto.
          apply free_block_allocated in H.
          destruct H.
          eapply fin_inf_byte_allocated in H; eauto.
        }

        { (* Big pointer, shouldn't be allocated. *)
          exfalso.
          eapply ptr_in_memstate_heap_inf_fin_exists in H; eauto.
          destruct H as (?&?&?).
          apply free_block_allocated in H0.
          destruct H0 as (?&?).
          epose proof fin_inf_byte_allocated_exists _ _ _ _ MSR H0 as (?&?&?).
          red in H.
          rewrite CONV in H.
          discriminate.
        }
      }
    - intros ptr H.
      { destruct (InfToFinAddrConvert.addr_convert ptr) eqn:CONV.
        { (* ptr in finite range *)
          eapply ptr_in_memstate_heap_inf_fin in H; eauto.
          apply free_bytes_freed in H.
          eapply fin_inf_byte_not_allocated in H; eauto.
          apply lift_MemState_refine_prop.
        }

        { (* Big pointer, shouldn't be allocated. *)
          exfalso.
          eapply ptr_in_memstate_heap_inf_fin_exists in H; eauto.
          destruct H as (?&?&?).
          apply free_block_allocated in H0.
          destruct H0 as (?&?).
          epose proof fin_inf_byte_allocated_exists _ _ _ _ MSR H0 as (?&?&?).
          red in H.
          rewrite CONV in H.
          discriminate.
        }
      }
    - intros ptr aid H.
      { destruct (InfToFinAddrConvert.addr_convert ptr) eqn:CONV.
        { (* ptr in finite range *)
          split; intros ALLOC.
          - eapply fin_inf_byte_allocated; eauto.
            apply lift_MemState_refine_prop.
            apply free_non_block_bytes_preserved.
            + intros CONTRA.
              eapply ptr_in_memstate_heap_fin_inf in CONTRA; eauto.
            + eapply inf_fin_byte_allocated; eauto.
          - eapply fin_inf_byte_allocated; eauto.
            apply free_non_block_bytes_preserved.
            + intros CONTRA.
              eapply ptr_in_memstate_heap_fin_inf in CONTRA; eauto.
            + eapply inf_fin_byte_allocated; eauto.
              apply lift_MemState_refine_prop.
        }

        { (* Big pointer, shouldn't be allocated. *)
          split; intros ALLOC.
          - eapply inf_fin_byte_allocated_exists in ALLOC; eauto.
            destruct ALLOC as (?&?&?).
            rewrite CONV in H0; discriminate.
          - eapply inf_fin_byte_allocated_exists in ALLOC; eauto.
            destruct ALLOC as (?&?&?).
            rewrite CONV in H0; discriminate.
            apply lift_MemState_refine_prop.
        }
      }
    - intros ptr byte H.
      { destruct (InfToFinAddrConvert.addr_convert ptr) eqn:CONV.
        { (* ptr in finite range *)
          split; intros RBS.
          - pose proof inf_fin_read_byte_spec MSR CONV RBS as (byte_fin&RBS_FIN&BYTE_REF).
            eapply free_non_frame_bytes_read in RBS_FIN.
            2: {
              intros CONTRA.
              eapply ptr_in_memstate_heap_fin_inf in CONTRA; eauto.
            }
            eapply fin_inf_read_byte_spec; eauto.
            apply lift_MemState_refine_prop.
          - pose proof (lift_MemState_refine_prop ms_fin_final) as MSR'.
            epose proof inf_fin_read_byte_spec MSR' CONV RBS as (byte_fin&RBS_FIN&BYTE_REF).
            eapply free_non_frame_bytes_read in RBS_FIN.
            2: {
              intros CONTRA.
              eapply ptr_in_memstate_heap_fin_inf in CONTRA; eauto.
            }
            eapply fin_inf_read_byte_spec; eauto.
        }

        { (* Big pointer, shouldn't be allocated. *)
          split; intros ALLOC.
          - eapply inf_fin_read_byte_spec_exists in ALLOC; eauto.
            destruct ALLOC as (?&?&?&?&?).
            red in H2.
            rewrite CONV in H2; discriminate.
          - eapply inf_fin_read_byte_spec_exists in ALLOC; eauto.
            destruct ALLOC as (?&?&?&?&?).
            red in H2.
            rewrite CONV in H2; discriminate.
            apply lift_MemState_refine_prop.
        }
      }
    - clear - PTR_REF MSR free_block.
      intros h1 h2 H1 H2.
      cbn.

      apply MemState_refine_prop_heap_preserved in MSR.
      red in MSR.

      destruct ms_fin_start. destruct ms_memory_stack.
      rename memory_stack_heap into h_fin_start.
      destruct ms_inf_start. destruct ms_memory_stack.
      rename memory_stack_heap into h_inf_start.
      destruct ms_fin_final. destruct ms_memory_stack.
      rename memory_stack_heap into h_fin_final.
      cbn in *.
      unfold Memory64BitIntptr.MMEP.MMSP.memory_stack_heap_prop, MemoryBigIntptr.MMEP.MMSP.memory_stack_heap_prop in *.
      cbn in *.
      cbn in *.

      eapply free_block_prop_fin_inf; eauto.
      3: {
        eapply free_block; reflexivity.
      }

      { red.
        symmetry.
        apply MSR; auto.
      }

      { red.
        symmetry.
        auto.
      }
    - (* Free operation invariants *)
      clear - MSR free_invariants.
      destruct free_invariants.
      split.
      + eapply fin_inf_preserve_allocation_ids; eauto.
        apply lift_MemState_refine_prop.
      + eapply fin_inf_frame_stack_preserved; eauto.
        apply lift_MemState_refine_prop.
  Qed.

  Lemma handle_free_fin_inf :
    forall {ms_fin_start ms_fin_final ms_inf_start res_fin args_fin args_inf},
      MemState_refine_prop ms_inf_start ms_fin_start ->
      Forall2 DVC1.dvalue_refine_strict args_inf args_fin ->
      Memory64BitIntptr.MMEP.MemSpec.handle_free_prop args_fin ms_fin_start (ret (ms_fin_final, res_fin)) ->
      exists res_inf ms_inf_final,
        MemoryBigIntptr.MMEP.MemSpec.handle_free_prop args_inf ms_inf_start (ret (ms_inf_final, res_inf)) /\
          res_inf = res_fin /\
          MemState_refine_prop ms_inf_final ms_fin_final.
  Proof.
    intros ms_fin_start ms_fin_final ms_inf_start res_fin args_fin args_inf MSR ARGS HANDLE.
    red in HANDLE.
    destruct args_fin; try contradiction; inv ARGS.
    destruct d; try contradiction.
    destruct args_fin; try contradiction.
    inv H3.
    rename H2 into ADDR.
    rename x into inf_addr.
    rename a into ptr_fin.

    apply dvalue_refine_strict_addr_r_inv in ADDR as (ptr_inf&PTR&PTR_REF);
      subst.
    cbn in *.

    epose proof handle_free_spec_fin_inf MSR PTR_REF HANDLE.
    destruct res_fin.
    exists tt.
    destruct H as (ms_inf_final&?&?).
    exists ms_inf_final; auto.
  Qed.

  (* TODO: Lemma about lifting intrinsic handlers *)
  (* TODO: Move this *)
  Lemma handle_intrinsic_fin_inf :
    forall {t f args args0 ms_fin ms_fin' ms_inf d_fin}
      (ARGS: Forall2 DVCInfFin.dvalue_refine_strict args0 args),
      MemState_refine_prop ms_inf ms_fin ->
      Memory64BitIntptr.MMEP.MemSpec.handle_intrinsic_prop
        LLVMParams64BitIntptr.Events.DV.dvalue
        (LLVMParams64BitIntptr.Events.Intrinsic t f args) ms_fin (ret (ms_fin', d_fin)) ->
      exists d_inf ms_inf',
        MemoryBigIntptr.MMEP.MemSpec.handle_intrinsic_prop DVCInfFin.DV1.dvalue
          (InterpreterStackBigIntptr.LP.Events.Intrinsic t f args0) ms_inf
          (ret (ms_inf', d_inf)) /\
          DVC1.dvalue_refine_strict d_inf d_fin /\
          MemState_refine_prop ms_inf' ms_fin'.
  Proof.
    intros t f args args0 ms_fin ms_fin' ms_inf d_fin ARGS MSR INTRINSIC.

    red in INTRINSIC.
    unfold MemoryBigIntptr.MMEP.MemSpec.handle_intrinsic_prop.
    break_match.
    { (* Memcpy *)
      eapply MemPropT_fin_inf_bind.
      4: apply INTRINSIC.
      all: eauto.

      { (* MA *)
        intros a_fin ms_fin_ma MEMCPY.
        eapply handle_memcpy_fin_inf; eauto.
      }

      intros ms_inf0 ms_fin0 ms_fin'0 a_fin a_inf b_fin _ MSR' EQV.
      cbn in EQV.
      destruct EQV; subst.

      cbn.
      exists LLVMParamsBigIntptr.Events.DV.DVALUE_None.
      exists ms_inf0.
      split; auto.
      split; auto.
      rewrite DVCInfFin.dvalue_refine_strict_equation.
      rewrite DVC1.dvalue_convert_strict_equation.
      reflexivity.
    }

    break_match.
    { (* Malloc *)
      eapply MemPropT_fin_inf_bind.
      4: apply INTRINSIC.
      all: eauto.

      { (* MA: handle_malloc_prop *)
        intros a_fin ms_fin_ma HANDLE_MALLOC.
        eapply handle_malloc_fin_inf; eauto.
      }

      intros ms_inf0 ms_fin0 ms_fin'0 a_fin a_inf b_fin H H0 H1.
      cbn in H, H1.
      destruct H1; subst.
      do 2 eexists; cbn; split; auto.
      split; auto.
      rewrite DVC1.dvalue_refine_strict_equation, DVC1.dvalue_convert_strict_equation.
      cbn.
      rewrite H.
      auto.
    }

    break_match.
    { (* Free *)
      eapply MemPropT_fin_inf_bind.
      4: apply INTRINSIC.
      all: eauto.

      { (* MA: handle_free_prop *)
        intros a_fin ms_fin_ma HANDLE_FREE.
        eapply handle_free_fin_inf; eauto.
      }

      intros ms_inf0 ms_fin0 ms_fin'0 a_fin a_inf b_fin H H0 H1.
      cbn in H, H1.
      destruct H1; subst.
      do 2 eexists; cbn; split; auto.
      split; auto.
      rewrite DVC1.dvalue_refine_strict_equation, DVC1.dvalue_convert_strict_equation.
      cbn.
      auto.
    }

    (* Unknown intrinsic *)
    cbn in *; auto.
    contradiction.
  Qed.

  (* TODO: Prove this *)
  Lemma serialize_sbytes_fin_inf :
    forall {ms_fin_start ms_fin_final ms_inf_start uv_fin uv_inf t bytes_fin},
      MemState_refine_prop ms_inf_start ms_fin_start ->
      DVC1.uvalue_refine_strict uv_inf uv_fin ->
      Memory64BitIntptr.MMEP.MemSpec.MemHelpers.serialize_sbytes (M:=MemPropT Memory64BitIntptr.MMEP.MMSP.MemState) uv_fin t ms_fin_start
        (ret (ms_fin_final, bytes_fin)) ->
      exists
        (bytes_inf : list MemoryBigIntptr.MP.BYTE_IMPL.SByte) (ms_inf_final : MemoryBigIntptr.MMEP.MMSP.MemState),
        MemoryBigIntptr.MMEP.MemSpec.MemHelpers.serialize_sbytes (M:=MemPropT MemoryBigIntptr.MMEP.MMSP.MemState) uv_inf t ms_inf_start
          (ret (ms_inf_final, bytes_inf)) /\
          sbytes_refine bytes_inf bytes_fin /\
          MemState_refine_prop ms_inf_final ms_fin_final.
  Proof.
    intros ms_fin_start ms_fin_final ms_inf_start uv_fin uv_inf t bytes_fin MSR UV_REF SERIALIZE.
  Admitted.

  Lemma handle_store_fin_inf :
    forall {t addr_fin addr_inf uv_fin uv_inf ms_fin_start ms_fin_final ms_inf_start res_fin},
      MemState_refine_prop ms_inf_start ms_fin_start ->
      DVC1.dvalue_refine_strict addr_inf addr_fin ->
      DVC1.uvalue_refine_strict uv_inf uv_fin ->
      Memory64BitIntptr.MMEP.MemSpec.handle_memory_prop unit
        (LLVMParams64BitIntptr.Events.Store t addr_fin uv_fin) ms_fin_start (ret (ms_fin_final, res_fin)) ->
      exists res_inf ms_inf_final,
        MemoryBigIntptr.MMEP.MemSpec.handle_memory_prop unit
          (LLVMParamsBigIntptr.Events.Store t addr_inf uv_inf) ms_inf_start (ret (ms_inf_final, res_inf)) /\
          res_inf = res_fin /\
          MemState_refine_prop ms_inf_final ms_fin_final.
  Proof.
    intros t addr_fin addr_inf uv_fin uv_inf ms_fin_start ms_fin_final ms_inf_start res_fin MSR ADDR_REF VALUE_REF HANDLE.

    red in HANDLE.
    induction addr_fin;
      try
        solve
        [ rewrite DVC1.dvalue_refine_strict_equation in ADDR_REF;
          first
            [ apply dvalue_convert_strict_i1_inv in ADDR_REF
            | apply dvalue_convert_strict_i8_inv in ADDR_REF
            | apply dvalue_convert_strict_i32_inv in ADDR_REF
            | apply dvalue_convert_strict_i64_inv in ADDR_REF
            | apply dvalue_convert_strict_iptr_inv in ADDR_REF
            | apply dvalue_convert_strict_addr_inv in ADDR_REF
            | apply dvalue_convert_strict_double_inv in ADDR_REF
            | apply dvalue_convert_strict_float_inv in ADDR_REF
            | apply dvalue_convert_strict_poison_inv in ADDR_REF
            | apply dvalue_convert_strict_oom_inv in ADDR_REF
            | apply dvalue_convert_strict_none_inv in ADDR_REF
            | apply dvalue_convert_strict_struct_inv in ADDR_REF
            | apply dvalue_convert_strict_packed_struct_inv in ADDR_REF
            | apply dvalue_convert_strict_array_inv in ADDR_REF
            | apply dvalue_convert_strict_vector_inv in ADDR_REF
            ];
          first
            [ destruct ADDR_REF as (?&?&?); subst
            | inv ADDR_REF
            ];

          exists tt; destruct res_fin;
          exists (lift_MemState ms_fin_final);
          cbn; repeat (split; auto)
        ].

    (* Main successful portion of the lemma *)
    unfold MemoryBigIntptr.MMEP.MemSpec.handle_memory_prop.
    eapply dvalue_refine_strict_addr_r_inv in ADDR_REF as (ptr_inf&PTR_INF&PTR_REF).
    subst.

    eapply MemPropT_fin_inf_bind.
    4: apply HANDLE.
    all: eauto.

    { (* MA: serialize_sbytes *)
      intros a_fin ms_fin_ma SERIALIZE.
      eapply serialize_sbytes_fin_inf; eauto.
    }

    intros ms_inf ms_fin ms_fin' a_fin a_inf b_fin H H0 H1.
    eapply fin_inf_write_bytes_spec; eauto.
  Qed.

  (* TODO: Prove this *)
  Lemma deserialize_sbytes_fin_inf :
    forall {bytes_fin bytes_inf t res_fin},
      sbytes_refine bytes_inf bytes_fin ->
      Memory64BitIntptr.MMEP.MemSpec.MemHelpers.deserialize_sbytes bytes_fin t = inr res_fin ->
      exists res_inf,
        MemoryBigIntptr.MMEP.MemSpec.MemHelpers.deserialize_sbytes bytes_inf t = inr res_inf /\
          DVC1.uvalue_refine_strict res_inf res_fin.
  Proof.
  Admitted.

  (* TODO: Prove this *)
  Lemma deserialize_sbytes_fail_fin_inf :
    forall {bytes_fin bytes_inf t s},
      sbytes_refine bytes_inf bytes_fin ->
      Memory64BitIntptr.MMEP.MemSpec.MemHelpers.deserialize_sbytes bytes_fin t = inl s ->
      MemoryBigIntptr.MMEP.MemSpec.MemHelpers.deserialize_sbytes bytes_inf t = inl s.
  Proof.
    (* TODO: why is all of this so SLOW??? *)
    (* intros bytes_fin bytes_inf t s BYTES. *)
    (* induction BYTES; intros DESERIALIZE. *)
    (* - rewrite Memory64BitIntptr.MMEP.MemSpec.MemHelpers.deserialize_sbytes_equation in DESERIALIZE. *)
    (*   rewrite MemoryBigIntptr.MMEP.MemSpec.MemHelpers.deserialize_sbytes_equation. *)
    (*   generalize dependent s. *)
    (*   induction t; intros s DESERIALIZE; *)
    (*     inv DESERIALIZE; auto. *)

    (*   + remember (LLVMParamsBigIntptr.SIZEOF.sizeof_dtyp t) as sz_t. *)
    (*     destruct (monad_fold_right *)
    (*                 (fun (acc : list LLVMParams64BitIntptr.Events.DV.uvalue) (idx : N) => *)
    (*                    match *)
    (*                      Memory64BitIntptr.MMEP.MemSpec.MemHelpers.deserialize_sbytes *)
    (*                        (between (idx * sz_t) ((idx + 1) * sz_t) []) t *)
    (*                    with *)
    (*                    | inl v => inl v *)
    (*                    | inr v => inr (v :: acc) *)
    (*                    end) (Nseq 0 (N.to_nat sz)) []) eqn:FOLD. *)

    (*     unfold between in FOLD. *)
    (*     unfold drop in FOLD. *)
    (*     unfold take in FOLD. *)
    (*     rewrite Memory64BitIntptr.MMEP.MemSpec.MemHelpers.deserialize_sbytes_equation in FOLD. *)
    (*     break_inner_match_hyp. *)
    (*     erewrite IHt in FOLD. *)
    (*     cbn in FOLD. *)
    (*     break_match_hyp. *)
  Admitted.

  Lemma handle_load_fin_inf :
    forall {t addr_fin addr_inf ms_fin_start ms_fin_final ms_inf_start res_fin},
      MemState_refine_prop ms_inf_start ms_fin_start ->
      DVC1.dvalue_refine_strict addr_inf addr_fin ->
      Memory64BitIntptr.MMEP.MemSpec.handle_memory_prop _
        (LLVMParams64BitIntptr.Events.Load t addr_fin) ms_fin_start (ret (ms_fin_final, res_fin)) ->
      exists res_inf ms_inf_final,
        MemoryBigIntptr.MMEP.MemSpec.handle_memory_prop _
          (LLVMParamsBigIntptr.Events.Load t addr_inf) ms_inf_start (ret (ms_inf_final, res_inf)) /\
          DVC1.uvalue_refine_strict res_inf res_fin /\
          MemState_refine_prop ms_inf_final ms_fin_final.
  Proof.
    intros t addr_fin addr_inf ms_fin_start ms_fin_final ms_inf_start res_fin MSR ADDR_REF HANDLE.

    red in HANDLE.
    induction addr_fin;
      try
        solve
        [ rewrite DVC1.dvalue_refine_strict_equation in ADDR_REF;
          first
            [ apply dvalue_convert_strict_i1_inv in ADDR_REF
            | apply dvalue_convert_strict_i8_inv in ADDR_REF
            | apply dvalue_convert_strict_i32_inv in ADDR_REF
            | apply dvalue_convert_strict_i64_inv in ADDR_REF
            | apply dvalue_convert_strict_iptr_inv in ADDR_REF
            | apply dvalue_convert_strict_addr_inv in ADDR_REF
            | apply dvalue_convert_strict_double_inv in ADDR_REF
            | apply dvalue_convert_strict_float_inv in ADDR_REF
            | apply dvalue_convert_strict_poison_inv in ADDR_REF
            | apply dvalue_convert_strict_oom_inv in ADDR_REF
            | apply dvalue_convert_strict_none_inv in ADDR_REF
            | apply dvalue_convert_strict_struct_inv in ADDR_REF
            | apply dvalue_convert_strict_packed_struct_inv in ADDR_REF
            | apply dvalue_convert_strict_array_inv in ADDR_REF
            | apply dvalue_convert_strict_vector_inv in ADDR_REF
            ];
          first
            [ destruct ADDR_REF as (?&?&?); subst
            | inv ADDR_REF
            ];

          exists (fin_to_inf_uvalue res_fin);
          exists (lift_MemState ms_fin_final);
          cbn; repeat (split; auto);
          apply fin_to_inf_uvalue_refine_strict
        ].

    (* Main successful portion of the lemma *)
    unfold MemoryBigIntptr.MMEP.MemSpec.handle_memory_prop.
    eapply dvalue_refine_strict_addr_r_inv in ADDR_REF as (ptr_inf&PTR_INF&PTR_REF).
    subst.

    eapply MemPropT_fin_inf_bind.
    4: apply HANDLE.
    all: eauto.

    { (* MA: read_bytes_spec *)
      intros a_fin ms_fin_ma READ.
      eapply fin_inf_read_bytes_spec; eauto.
      apply READ.
    }

    intros ms_inf ms_fin ms_fin' a_fin a_inf b_fin BYTES_REF MSR_LOAD DESERIALIZE.
    unfold lift_err_RAISE_ERROR in *.

    break_match_hyp.
    - eapply deserialize_sbytes_fail_fin_inf in Heqs; eauto.
      rewrite Heqs.
      do 2 eexists.
      split; eauto.
      split.
      apply fin_to_inf_uvalue_refine_strict.
      apply lift_MemState_refine_prop.
    - eapply deserialize_sbytes_fin_inf in Heqs; eauto.
      destruct Heqs as (?&?&?).
      cbn in DESERIALIZE.
      destruct DESERIALIZE; subst.
      rewrite H.
      exists x. exists ms_inf.
      split; cbn; auto.
  Qed.

  Lemma model_E1E2_23_orutt_strict :
    forall t_inf t_fin sid ms1 ms2,
      L2_E1E2_orutt_strict t_inf t_fin ->
      MemState_refine_prop ms1 ms2 ->
      L3_E1E2_orutt_strict (InfMemInterp.interp_memory_prop TLR_INF.R.refine_res2 t_inf sid ms1) (FinMemInterp.interp_memory_prop TLR_FIN.R.refine_res2 t_fin sid ms2).
  Proof.
    intros t_inf t_fin sid ms1 ms2 REL MSR.
    red.
    red in REL.
    (* red in REL. *)

    unfold L3_E1E2_orutt_strict.
    intros t_fin2 FIN_HANDLED.

    exists (get_inf_tree t_fin2).
    split.
    { red.
      revert FIN_HANDLED.
      revert REL.

      rewrite (itree_eta_ t_fin).
      rewrite (itree_eta_ t_fin2).
      rewrite (itree_eta_ t_inf).

      genobs t_fin ot_fin.
      genobs t_fin2 ot_fin2.
      genobs t_inf ot_inf.
      clear t_inf Heqot_inf.
      clear t_fin Heqot_fin.
      clear t_fin2 Heqot_fin2.

      revert ot_inf ot_fin ot_fin2.
      pcofix CIH.
      intros ot_inf ot_fin ot_fin2 REL RUN.

      punfold REL.
      red in REL.
      cbn in REL.

      remember (upaco2
                  (orutt_ L2_refine_strict L2_res_refine_strict
                     (local_refine_strict × stack_refine_strict
                        × (global_refine_strict × DVCInfFin.dvalue_refine_strict))) bot2) as r'.
      revert Heqr'.

      dependent induction REL; intros Heqr'.
      - subst.
        apply interp_memory_prop_ret_inv in RUN.
        destruct RUN as [[r3 [REQ EQ]] | [A [e [k EUTT]]]]; subst.
        2: {
          eapply paco2_mon_bot; eauto.
          rewrite EUTT.
          pstep; red; cbn.
          econstructor.
          destruct e.
          pstep; red; cbn.
          constructor.
          intros [] _.
        }

        (assert (eutt eq (get_inf_tree {| _observe := ot_fin2 |}) (get_inf_tree (ret r3)))).
        { rewrite <- EQ.
          reflexivity.
        }

        eapply paco2_mon_bot; eauto.
        rewrite H0.

        destruct r3. repeat (destruct p; subst).
        destruct p0.

        destruct r1 as [[lenv lstack] [stack res]].
        destruct H as [[LR SR] [GR DR]]. cbn in *.

        pstep; red; cbn.
        constructor.

        red.
        constructor; cbn; red; auto.
        constructor; cbn.
        red. auto.

        destruct REQ as [_ [_ REQ]].
        destruct r2 as [l' [s' r2]].
        cbn in *. subst.
        pose proof (fin_to_inf_dvalue_refine_strict d).

        apply fin_to_inf_dvalue_refine_strict'; auto.
      - punfold RUN.
        red in RUN.
        cbn in RUN.

        assert (DEC: (exists m3, ot_fin2 = TauF m3) \/ (forall m3, ot_fin2 <> TauF m3)).
        { destruct ot_fin2; eauto; right; red; intros; inversion H0. }

        destruct DEC as [EQ | EQ].
        { destruct EQ as [m3 EQ].
          subst.
          pstep; red; cbn.
          constructor.
          right.
          rewrite (itree_eta_ m1).
          rewrite (itree_eta_ m3).
          eapply CIH.

          pclearbot.
          punfold H; red in H.
          pstep. red. cbn.
          eauto.

          red.
          rewrite <- itree_eta_.
          rewrite <- itree_eta_.

          rewrite <- tau_eutt.
          rewrite <- (tau_eutt m3).
          pstep; red; cbn.
          auto.
        }

        inversion RUN; subst.
        + specialize (EQ t2).
          contradiction.
        + pstep; red; cbn.
          constructor; auto.

          rewrite (itree_eta_ m2) in H.
          rewrite (itree_eta_ m2) in RUN.
          genobs m2 om2.
          setoid_rewrite <- Heqom2 in HS.
          clear Heqom2.
          clear m2.
          induction HS; subst.
          -- inversion RUN; subst.
             cbn in *.
             inversion HS; subst.

             pclearbot.
             punfold H.
             red in H.

             { dependent induction H.
               - rewrite <- x.
                 constructor.
                 destruct H as [[LR SR] [GR DR]]. cbn in *; subst; auto.
                 destruct r2 as [l' [s' r2]].
                 destruct r2.
                 destruct p.
                 destruct p0.
                 cbn.
                 cbn in *.
                 destruct r0.
                 destruct p, p0.
                 constructor; auto.
                 constructor; auto.
                 constructor; auto.
                 cbn. red. auto.
                 cbn in *.
                 destruct r1, p, p0. cbn in *.
                 destruct REL as [_ [_ REL]].
                 cbn in REL. subst.
                 apply fin_to_inf_dvalue_refine_strict'. auto.
               - rewrite <- x.
                 constructor; eauto.
             }

             { rewrite itree_eta in HT1.
               rewrite H2 in HT1.
               pinversion HT1.
             }

             { rewrite itree_eta in HT1.
               rewrite H2 in HT1.
               pinversion HT1.
             }
          -- specialize (EQ t2).
             contradiction.
          -- eapply IHHS; eauto.
             left.
             pclearbot.
             assert (orutt (OOM:=OOME) (@L2_refine_strict) (@L2_res_refine_strict) (local_refine_strict × stack_refine_strict
                                                                                      × (global_refine_strict × DVCInfFin.dvalue_refine_strict)) m1 (Tau t1)).
             { apply H.
             }
             setoid_rewrite tau_eutt in H0.
             rewrite <- itree_eta_.
             apply H0.
          -- specialize (EQ t2).
             contradiction.
          -- (* Vis OOM *)
            rewrite itree_eta in HT1.
            genobs t2 ot2. clear t2 Heqot2.
            punfold HT1; red in HT1; cbn in HT1.
            dependent induction HT1.
            ++ destruct e.
               econstructor.
               pstep; red; cbn.
               constructor.
               intros [] _.
            ++ specialize (EQ t0); contradiction.
          -- (* Vis *)
            { rewrite itree_eta in H1.
              genobs t2 ot2.
              clear t2 Heqot2.
              dependent induction RUN; subst.
              - (* Tau Tau *)
                specialize (EQ t2).
                contradiction.
              - (* TauL *)
                clear IHRUN.
                pclearbot.
                apply orutt_inv_Vis_r in H.
                destruct H as [[U1 [e1 [k3 [M1 [EV_REL K_RUTT]]]]] | OOM].
                2: {
                  destruct OOM as [o OOM].
                  inv OOM.
                  repeat red in H0.
                  rewrite H0 in H1.
                  setoid_rewrite bind_trigger in H1.
                  setoid_rewrite bind_vis in H1.
                  punfold H1; red in H1; cbn in H1.
                  dependent induction H1.
                  - destruct o.
                    eapply Interp_Memory_PropT_Vis_OOM.
                    rewrite get_inf_tree_equation.
                    cbn.
                    unfold raiseOOM.
                    rewrite bind_trigger.
                    reflexivity.
                  - specialize (EQ t1). contradiction.
                }

                punfold M1; red in M1; cbn in M1.
                genobs m1 om1.
                clear m1 Heqom1.
                dependent induction M1.
                + (* om1 = Vis *)
                  rename H1 into VIS_HANDLED.

                  (* Need to break apart events e / e1 to figure out
                what event we're dealing with. *)
                  red in EV_REL.
                  destruct e, e1; try destruct e, e0; cbn in EV_REL;
                    move EV_REL after VIS_HANDLED;
                    repeat (first [destruct s | destruct i | destruct e | destruct s0 | destruct m | destruct m0]; try contradiction); cbn in *.

                  { (* ExternalCallE *)
                    destruct EV_REL as (T&F&ARGS); subst.
                    red in H0.
                    rewrite H0 in VIS_HANDLED.

                    setoid_rewrite bind_trigger in VIS_HANDLED.
                    setoid_rewrite bind_vis in VIS_HANDLED.
                    setoid_rewrite bind_ret_l in VIS_HANDLED.
                    punfold VIS_HANDLED; red in VIS_HANDLED; cbn in VIS_HANDLED.
                    dependent induction VIS_HANDLED.
                    { eapply Interp_Memory_PropT_Vis with
                        (k2:=(fun '(ms_inf, (sid', dv_inf)) =>
                                match DVCInfFin.dvalue_convert_strict dv_inf with
                                | NoOom dv_fin => get_inf_tree (k5 dv_fin)
                                | Oom s => raiseOOM s
                                end)
                        ).
                      2: {
                        cbn. red.
                        reflexivity.
                      }
                      2: {
                        cbn.
                        setoid_rewrite bind_trigger.
                        pstep; red; cbn.

                        pose proof (fin_to_inf_uvalue_refine_strict' _ _ F).
                        rewrite <- H.

                        rewrite Forall2_map_eq with (l2:=args0).
                        2: {
                          eapply Forall2_flip.
                          eapply Util.Forall2_impl; [| apply ARGS].
                          intros a b H1.
                          red.
                          symmetry.
                          apply fin_to_inf_dvalue_refine_strict'.
                          auto.
                        }

                        constructor.
                        intros v.
                        red.

                        left.
                        setoid_rewrite bind_ret_l.
                        cbn.
                        break_match_goal.
                        apply paco2_eqit_refl.
                        rewrite get_inf_tree_equation; cbn.
                        apply paco2_eqit_refl.
                      }

                      intros a (ms'&sid'&b) RET H1 H2; cbn in *; subst.
                      break_match_goal.
                      2: {
                        (* OOM *)
                        cbn.
                        left.
                        pstep; red; cbn.
                        observe_vis; solve_interp_prop_oom.
                      }

                      (* Need to figure out how k0 and k5 are related *)
                      (*
                      REL : forall v : InterpreterStackBigIntptr.LP.Events.DV.dvalue,
                          id (upaco2 (eqit_ eq true true id) bot2) (k0 v) (k3 v)

                      REL0 : forall v : dvalue,
                          id (upaco2 (eqit_ eq true true id) bot2) (k5 v) (k2 (s2, (s1, v)))

                      HK : forall (a : dvalue) (b : Memory64BitIntptr.MMEP.MMSP.MemState * (MemPropT.store_id * dvalue)),
                        Returns a (trigger (inl1 (ExternalCall t f args))) ->
                        Returns b ta ->
                        a = snd (snd b) ->
                        upaco2
                          (interp_memory_PropT_ FinMemInterp.interp_memory_prop_h
                          (fun (x : res_L2) '(_, (_, y)) => TLR_FIN.R.refine_res2 x y) true true) bot2
                          (k1 a) (k2 b)

                      K_RUTT : forall (v1 : InterpreterStackBigIntptr.LP.Events.DV.dvalue) (v2 : dvalue),
                         t = t /\
                         DVCInfFin.uvalue_refine_strict f0 f /\
                         Forall2 DVCInfFin.dvalue_refine_strict args0 args /\ DVCInfFin.dvalue_refine_strict v1 v2 ->
                         orutt L2_refine_strict L2_res_refine_strict
                         (local_refine_strict × stack_refine_strict
                         × (global_refine_strict × DVCInfFin.dvalue_refine_strict)) (k3 v1)
                         (k1 v2)


                       *)

                      pclearbot.
                      right.
                      rewrite (itree_eta_ (k0 b)).
                      rewrite (itree_eta_ (k5 d)).

                      eapply CIH;
                        repeat rewrite <- itree_eta_.

                      2: {
                        red.
                        rewrite REL0.
                        specialize (HK d (s2, (s1, d))).
                        forward HK.
                        { eapply ReturnsVis.
                          pstep; red; cbn.
                          constructor.
                          intros v. red.
                          left; apply paco2_eqit_refl.
                          constructor.
                          reflexivity.
                        }
                        forward HK.
                        { rewrite H0.
                          rewrite bind_trigger.
                          eapply ReturnsVis.
                          reflexivity.
                          cbn.
                          constructor.
                          reflexivity.
                        }
                        forward HK; cbn; auto.
                        pclearbot.
                        apply HK.
                      }

                      rewrite REL.
                      eapply K_RUTT; split; auto.
                    }
                    { specialize (EQ t1).
                      contradiction.
                    }
                  }

                  { (* Intrinsic *)
                    destruct EV_REL as (T&F&ARGS); subst.
                    red in H0.
                    red in H0.
                    destruct H0 as [UB | [ERR | [OOM | H0]]].
                    { (* Handler raises UB *)
                      destruct UB as [ub_msg INTRINSIC].
                      red in INTRINSIC.
                      break_match_hyp.
                      { (* memcpy *)
                        cbn in *.
                        destruct INTRINSIC as [HANDLER | [sab [[] [HANDLER []]]]].
                        red in HANDLER.
                        repeat (destruct ARGS;
                                [solve [ inversion HANDLER
                                       | red in HANDLER;
                                         repeat break_match_hyp; cbn in HANDLER; inversion HANDLER
                                   ]
                                |
                               ]).
                        repeat break_match_hyp; cbn in HANDLER; try contradiction.

                        { (* 32 bit *)
                          red in HANDLER.
                          break_match_hyp.
                          { (* Negative length UB *)
                            admit.
                          }

                          break_match_hyp.
                          2: {
                            (* Overlapping UB *)
                            admit.
                          }

                          (* No UB *)
                          (* May be UB in read / write... *)
                          cbn in HANDLER.
                          admit.
                        }

                        { (* 64 bit *)
                          admit.
                        }

                        { (* iptr *)
                          admit.
                        }
                      }

                      (* Not memcpy... *)
                      admit.
                    }

                    { (* Handler raises Error *)
                      destruct ERR as [err_msg [TA HANDLER]].
                      unfold raise_error in TA.
                      cbn in TA.
                      unfold LLVMEvents.raise in TA.
                      rewrite bind_trigger in TA.

                      rewrite TA in VIS_HANDLED.
                      rewrite bind_vis in VIS_HANDLED.

                      punfold VIS_HANDLED; red in VIS_HANDLED; cbn in VIS_HANDLED.
                      dependent induction VIS_HANDLED.
                      2: {
                        specialize (EQ t1); contradiction.
                      }

                      eapply Interp_Memory_PropT_Vis with (ta:=
                                                             vis (Throw err_msg)
                                                               (fun x : void =>
                                                                  match
                                                                    x
                                                                    return
                                                                    (itree
                                                                       (InterpreterStackBigIntptr.LP.Events.ExternalCallE +'
                                                                                                                             LLVMParamsBigIntptr.Events.PickUvalueE +' OOME +' UBE +' DebugE +' FailureE)
                                                                       (MemoryBigIntptr.MMEP.MMSP.MemState *
                                                                          (MemPropT.store_id * LLVMParamsBigIntptr.Events.DV.dvalue)))
                                                                  with
                                                                  end)).

                      3: {
                        rewrite get_inf_tree_equation.
                        cbn. unfold LLVMEvents.raise.
                        rewrite bind_trigger.
                        rewrite bind_vis.
                        pstep; red; cbn.
                        constructor.
                        intros [].
                      }

                      { intros a (ms_b, (sid_b, b)) RET1 RET2 AB.
                        cbn in AB; subst.

                        pclearbot.
                        right.
                        rewrite (itree_eta_ (k0 _)).
                        rewrite (itree_eta_).

                      (*   eapply CIH; *)
                      (*     repeat rewrite <- itree_eta_. *)

                      (*   2: { *)
                      (*     red. *)
                      (*     specialize (HK d (ms', (st1, d))). *)
                      (*     forward HK. *)
                      (*     { eapply ReturnsVis. *)
                      (*       pstep; red; cbn. *)
                      (*       constructor. *)
                      (*       intros v. red. *)
                      (*       left; apply paco2_eqit_refl. *)
                      (*       constructor. *)
                      (*       reflexivity. *)
                      (*     } *)
                      (*     forward HK. *)
                      (*     { rewrite H0. *)
                      (*       constructor. *)
                      (*       reflexivity. *)
                      (*     } *)
                      (*     forward HK; cbn; auto. *)
                      (*     pclearbot. *)
                      (*     rewrite MemState_fin_to_inf_to_fin in Heqo0; inv Heqo0. *)
                      (*     rewrite dvalue_fin_to_inf_to_fin in Heqo; inv Heqo. *)
                      (*     apply HK. *)
                      (*   } *)

                      (*   rewrite REL. *)
                      (*   eapply K_RUTT; split; auto. *)
                      (* } *)

                        (* eapply CIH. *)
                        admit.

                      }
                      admit.
                    }

                    { (* Handler raises OOM *)
                      destruct OOM as [oom_msg [TA HANDLER]].
                      unfold raise_oom in TA.
                      cbn in TA.
                      unfold raiseOOM in TA.
                      rewrite bind_trigger in TA.

                      rewrite TA in VIS_HANDLED.
                      rewrite bind_vis in VIS_HANDLED.

                      punfold VIS_HANDLED; red in VIS_HANDLED; cbn in VIS_HANDLED.
                      dependent induction VIS_HANDLED.
                      2: {
                        specialize (EQ t1); contradiction.
                      }

                      econstructor.
                      rewrite get_inf_tree_equation.
                      cbn.
                      unfold raiseOOM.
                      rewrite bind_trigger.
                      reflexivity.
                    }

                    (* Handler succeeds *)
                    destruct H0 as (st1&ms'&d&TA&INTRINSIC).
                    rewrite TA in VIS_HANDLED.
                    setoid_rewrite bind_ret_l in VIS_HANDLED.

                    { epose proof handle_intrinsic_fin_inf ARGS (lift_MemState_refine_prop s2) INTRINSIC as (dv_inf&ms_inf'&INTRINSIC_INF&DV_REF&MSR_INTRINSIC).

                      eapply Interp_Memory_PropT_Vis with
                        (k2:=(fun '(ms_inf, (sid', dv_inf)) =>
                                get_inf_tree (k2 (ms', (st1, d)))
                             )
                        )
                        (s1:=s1)
                        (s2:=lift_MemState s2).

                      2: {
                        cbn. red. red.
                        repeat right.
                        exists s1.
                        exists ms_inf'.
                        exists dv_inf.
                        split; eauto.
                        reflexivity.
                      }

                      2: {
                        cbn.
                        rewrite bind_ret_l.
                        rewrite VIS_HANDLED.
                        reflexivity.
                      }

                      (* Continuation for vis node *)
                      intros a b H H1 H2.
                      destruct b as [ms [sid' res]].
                      cbn in H1.
                      apply Returns_ret_inv in H1.
                      inv H1.

                      cbn.
                      rewrite (itree_eta_ (k0 dv_inf)).
                      rewrite (itree_eta_ (k2 (ms', (st1, d)))).
                      right.
                      eapply CIH.
                      2: {
                        repeat red.
                        specialize (HK d (ms', (st1, d))).
                        forward HK.
                        { eapply ReturnsVis.
                          unfold trigger.
                          reflexivity.
                          cbn.
                          constructor.
                          reflexivity.
                        }
                        forward HK.
                        { constructor.
                          auto.
                        }

                        forward HK; auto.
                        pclearbot.

                        repeat rewrite <- itree_eta.
                        apply HK.
                      }

                      specialize (REL dv_inf).
                      red in REL.
                      pclearbot.

                      repeat rewrite <- itree_eta.
                      rewrite REL.
                      eapply K_RUTT.
                      repeat (split; auto).
                    }
                  }

                  { (* MemPush *)
                    repeat red in H0.
                    rename s2 into m1.
                    destruct H0 as [UB | [ERR | [OOM | H0]]].
                    { (* Handler raises UB *)
                      destruct UB as [ub_msg UB].
                      cbn in UB.

                      (* TODO: look into lemmas like:

                         - get_consecutive_ptrs_no_ub
                         - allocate_bytes_spec_MemPropT_no_ub
                       *)
                      admit.
                    }

                    { (* Handler raises error *)
                      admit.
                    }

                    { (* Handler raises OOM *)
                      admit.
                    }

                    (* Handler succeeds *)
                    destruct H0 as [st' [ms_push [[] [TA PUSH_HANDLER]]]].
                    cbn in PUSH_HANDLER.

                    rewrite TA in VIS_HANDLED.
                    cbn in VIS_HANDLED.
                    rewrite bind_ret_l in VIS_HANDLED.


                    { epose proof mem_push_spec_fin_inf (lift_MemState_refine_prop m1) (lift_MemState_refine_prop ms_push) PUSH_HANDLER as PUSH_INF.

                      eapply Interp_Memory_PropT_Vis with
                        (k2:=(fun '(ms_inf, (sid', _)) =>
                                match convert_MemState ms_inf with
                                | NoOom ms_fin =>
                                    get_inf_tree (k2 (ms_fin, (st', tt)))
                                | Oom s => raiseOOM s
                                end)
                        )
                        (s1:=s1)
                        (s2:=lift_MemState m1).

                      2: {
                        cbn. red. red.
                        repeat right.
                        exists s1.
                        exists (lift_MemState ms_push).
                        exists tt.
                        split; try reflexivity.
                        cbn; auto.
                      }

                      2: {
                        cbn.
                        rewrite bind_ret_l.
                        rewrite MemState_fin_to_inf_to_fin.
                        rewrite VIS_HANDLED.
                        reflexivity.
                      }

                      (* Continuation for vis node *)
                      intros a b H H1 H2.
                      destruct b as [ms [sid' res]].
                      cbn in H1.
                      apply Returns_ret_inv in H1.
                      inv H1.

                      cbn.
                      rewrite MemState_fin_to_inf_to_fin.
                      rewrite (itree_eta_ (k0 tt)).
                      rewrite (itree_eta_ (k2 (ms_push, (st', tt)))).
                      right.
                      eapply CIH.
                      2: {
                        repeat red.
                        specialize (HK tt (ms_push, (st', tt))).
                        forward HK.
                        { eapply ReturnsVis.
                          unfold trigger.
                          reflexivity.
                          cbn.
                          constructor.
                          reflexivity.
                        }
                        forward HK.
                        { rewrite TA.
                          constructor.
                          reflexivity.
                        }

                        forward HK; auto.
                        pclearbot.

                        repeat rewrite <- itree_eta.
                        apply HK.
                      }

                      specialize (REL tt).
                      red in REL.
                      pclearbot.

                      repeat rewrite <- itree_eta.
                      rewrite REL.
                      eapply K_RUTT.
                      repeat (split; auto).
                    }
                  }

                  { (* MemPop *)
                    repeat red in H0.
                    destruct H0 as [UB | [ERR | [OOM | H0]]].
                    { (* Handler raises UB *)
                      admit.
                    }

                    { (* Handler raises error *)
                      admit.
                    }

                    { (* Handler raises OOM *)
                      admit.
                    }

                    (* Handler succeeds *)
                    destruct H0 as [st' [ms_pop [[] [TA POP_HANDLER]]]].
                    cbn in POP_HANDLER.

                    rewrite TA in VIS_HANDLED.
                    cbn in VIS_HANDLED.
                    rewrite bind_ret_l in VIS_HANDLED.

                    { eapply Interp_Memory_PropT_Vis with
                        (k2:=(fun '(ms_inf, (sid', _)) =>
                                match convert_MemState ms_inf with
                                | NoOom ms_fin =>
                                    get_inf_tree (k2 (ms_fin, (st', tt)))
                                | Oom s => raiseOOM s
                                end)
                        )
                        (s1:=s1)
                        (s2:=lift_MemState s2).

                      2: {
                        cbn. red. red.
                        repeat right.
                        exists s1.
                        exists (lift_MemState ms_pop).
                        exists tt.
                        split; try reflexivity.
                        cbn.

                        eapply mem_pop_spec_fin_inf; eauto; apply lift_MemState_refine_prop.
                      }

                      2: {
                        cbn.
                        rewrite bind_ret_l.
                        rewrite MemState_fin_to_inf_to_fin.
                        rewrite VIS_HANDLED.
                        reflexivity.
                      }

                      (* Continuation for vis node *)
                      intros [] b H H1 H2.
                      destruct b as [ms [sid' res]].
                      cbn in H1.
                      cbn in H2. inv H2.
                      apply Returns_ret_inv in H1.
                      inv H1.

                      cbn.
                      rewrite MemState_fin_to_inf_to_fin.
                      rewrite (itree_eta_ (k0 tt)).
                      rewrite (itree_eta_ (k2 (ms_pop, (st', tt)))).
                      right.
                      eapply CIH.
                      2: {
                        repeat red.
                        specialize (HK tt (ms_pop, (st', tt))).
                        forward HK.
                        { eapply ReturnsVis.
                          unfold trigger.
                          reflexivity.
                          cbn.
                          constructor.
                          reflexivity.
                        }
                        forward HK.
                        { rewrite TA.
                          constructor.
                          reflexivity.
                        }

                        forward HK; auto.
                        pclearbot.

                        repeat rewrite <- itree_eta.
                        apply HK.
                      }

                      specialize (REL tt).
                      red in REL.
                      pclearbot.

                      repeat rewrite <- itree_eta.
                      rewrite REL.
                      eapply K_RUTT.
                      repeat (split; auto).
                    }
                  }

                  { (* Alloca *)
                    repeat red in H0.
                    destruct H0 as [UB | [ERR | [OOM | H0]]].
                    { (* Handler raises UB *)
                      admit.
                    }

                    { (* Handler raises error *)
                      admit.
                    }

                    { (* Handler raises OOM *)
                      admit.
                    }

                    (* Handler succeeds *)
                    destruct H0 as [st' [ms_alloca [d [TA ALLOCA_HANDLER]]]].

                    rewrite TA in VIS_HANDLED.
                    cbn in VIS_HANDLED.
                    rewrite bind_ret_l in VIS_HANDLED.
                    destruct EV_REL as (?&?&?); subst.

                    { epose proof handle_alloca_fin_inf (lift_MemState_refine_prop s2) ALLOCA_HANDLER as (dv_inf&ms_inf'&ALLOCA_INF&DV_REF&MSR_ALLOCA).

                      eapply Interp_Memory_PropT_Vis with
                        (k2:=(fun '(ms_inf, (sid', dv_inf)) =>
                                get_inf_tree (k2 (ms_alloca, (st', d)))))
                        (s1:=s1)
                        (s2:=lift_MemState s2).

                      2: {
                        cbn. red. red.
                        repeat right.
                        exists s1.
                        exists ms_inf'.
                        exists dv_inf.
                        split; auto; reflexivity.
                      }

                      2: {
                        cbn.
                        rewrite bind_ret_l.
                        rewrite VIS_HANDLED.
                        reflexivity.
                      }

                      (* Continuation for vis node *)
                      intros a b H H0 H1.
                      destruct b as [ms [sid' res]].
                      cbn in H1; subst.
                      cbn in H0.
                      apply Returns_ret_inv in H0.
                      inv H0.

                      rewrite (itree_eta_ (k0 dv_inf)).
                      rewrite (itree_eta_ (k2 (ms_alloca, (st', d)))).
                      right.
                      eapply CIH.
                      2: {
                        repeat red.
                        specialize (HK d (ms_alloca, (st', d))).
                        forward HK.
                        { eapply ReturnsVis.
                          unfold trigger.
                          reflexivity.
                          cbn.
                          constructor.
                          reflexivity.
                        }
                        forward HK.
                        { rewrite TA.
                          constructor.
                          reflexivity.
                        }

                        forward HK; auto.
                        pclearbot.

                        repeat rewrite <- itree_eta.
                        apply HK.
                      }

                      specialize (REL dv_inf).
                      red in REL.
                      pclearbot.

                      repeat rewrite <- itree_eta.
                      rewrite REL.
                      eapply K_RUTT.
                      repeat (split; auto).
                    }
                  }

                  { (* Load *)
                    repeat red in H0.
                    destruct H0 as [UB | [ERR | [OOM | H0]]].
                    { (* Handler raises UB *)
                      admit.
                    }

                    { (* Handler raises error *)
                      admit.
                    }

                    { (* Handler raises OOM *)
                      admit.
                    }

                    (* Handler succeeds *)
                    destruct H0 as [st' [ms_load [uv_fin [TA LOAD_HANDLER]]]].

                    rewrite TA in VIS_HANDLED.
                    cbn in VIS_HANDLED.
                    rewrite bind_ret_l in VIS_HANDLED.
                    destruct EV_REL as (?&?); subst.

                    { epose proof handle_load_fin_inf (lift_MemState_refine_prop s2) H0 LOAD_HANDLER as (uv_inf&ms_inf'&LOAD_INF&UV_REF&MSR_LOAD).

                      eapply Interp_Memory_PropT_Vis with
                        (k2:=(fun '(ms_inf, (sid', uv_inf)) =>
                                get_inf_tree (k2 (ms_load, (st', uv_fin)))))
                        (s1:=s1)
                        (s2:=lift_MemState s2).

                      2: {
                        cbn. red. red.
                        repeat right.
                        exists s1.
                        exists ms_inf'.
                        exists uv_inf.
                        split; auto; reflexivity.
                      }

                      2: {
                        cbn.
                        rewrite bind_ret_l.
                        rewrite VIS_HANDLED.
                        reflexivity.
                      }

                      (* Continuation for vis node *)
                      intros a1 b H H2 H3.
                      destruct b as [ms [sid' res]].
                      cbn in H2; subst.
                      apply Returns_ret_inv in H2.
                      inv H2.
                      cbn.

                      rewrite (itree_eta_ (k0 uv_inf)).
                      rewrite (itree_eta_ (k2 (ms_load, (st', uv_fin)))).
                      right.
                      eapply CIH.
                      2: {
                        repeat red.
                        specialize (HK uv_fin (ms_load, (st', uv_fin))).
                        forward HK.
                        { eapply ReturnsVis.
                          unfold trigger.
                          reflexivity.
                          cbn.
                          constructor.
                          reflexivity.
                        }
                        forward HK.
                        { rewrite TA.
                          constructor.
                          reflexivity.
                        }

                        forward HK; auto.
                        pclearbot.

                        repeat rewrite <- itree_eta.
                        apply HK.
                      }

                      specialize (REL uv_inf).
                      red in REL.
                      pclearbot.

                      repeat rewrite <- itree_eta.
                      rewrite REL.
                      eapply K_RUTT.
                      repeat (split; auto).
                    }
                  }

                  { (* Store *)
                    repeat red in H0.
                    destruct H0 as [UB | [ERR | [OOM | H0]]].
                    { (* Handler raises UB *)
                      admit.
                    }

                    { (* Handler raises error *)
                      admit.
                    }

                    { (* Handler raises OOM *)
                      admit.
                    }

                    (* Handler succeeds *)
                    destruct H0 as [st' [ms_store [[] [TA STORE_HANDLER]]]].

                    rewrite TA in VIS_HANDLED.
                    cbn in VIS_HANDLED.
                    rewrite bind_ret_l in VIS_HANDLED.
                    destruct EV_REL as (?&?&?); subst.

                    { epose proof handle_store_fin_inf (lift_MemState_refine_prop s2) H0 H1 STORE_HANDLER as ([]&ms_inf'&STORE_INF&_&MSR_STORE).

                      eapply Interp_Memory_PropT_Vis with
                        (k2:=(fun '(ms_inf, (sid', dv_inf)) =>
                                get_inf_tree (k2 (ms_store, (st', tt)))))
                        (s1:=s1)
                        (s2:=lift_MemState s2).

                      2: {
                        cbn. red. red.
                        repeat right.
                        exists s1.
                        exists ms_inf'.
                        exists tt.
                        split; auto; reflexivity.
                      }

                      2: {
                        cbn.
                        rewrite bind_ret_l.
                        rewrite VIS_HANDLED.
                        reflexivity.
                      }

                      (* Continuation for vis node *)
                      intros a1 b H H2 H3.
                      destruct b as [ms [sid' res]].
                      cbn in H1; subst.
                      cbn in H2.
                      apply Returns_ret_inv in H2.
                      inv H0.
                      cbn.
                      destruct res.

                      rewrite (itree_eta_ (k0 tt)).
                      rewrite (itree_eta_ (k2 (ms_store, (st', tt)))).
                      right.
                      eapply CIH.
                      2: {
                        repeat red.
                        specialize (HK tt (ms_store, (st', tt))).
                        forward HK.
                        { eapply ReturnsVis.
                          unfold trigger.
                          reflexivity.
                          cbn.
                          constructor.
                          reflexivity.
                        }
                        forward HK.
                        { rewrite TA.
                          constructor.
                          reflexivity.
                        }

                        forward HK; auto.
                        pclearbot.

                        repeat rewrite <- itree_eta.
                        apply HK.
                      }

                      specialize (REL tt).
                      red in REL.
                      pclearbot.

                      repeat rewrite <- itree_eta.
                      rewrite REL.
                      eapply K_RUTT.
                      repeat (split; auto).
                    }
                  }

                  { (* Pick *)
                    admit.
                  }

                  { (* OOM *)
                    red in H0.
                    rewrite H0 in VIS_HANDLED.
                    setoid_rewrite bind_trigger in VIS_HANDLED.
                    rewrite bind_vis in VIS_HANDLED.

                    destruct t2; pinversion VIS_HANDLED; subst_existT.
                    { exfalso; eapply EQ; eauto. }
                    subst_existT.

                    destruct o.
                    eapply Interp_Memory_PropT_Vis_OOM.
                    cbn.
                    rewrite get_inf_tree_equation.
                    cbn.
                    unfold raiseOOM.
                    rewrite bind_trigger.
                    reflexivity.
                  }

                  { (* UBE *)
                    admit.
                  }

                  { (* DebugE *)
                    admit.
                  }

                  { (* FailureE *)
                    admit.
                  }

                + (* om1 = Tau *)
                  (* Tau on the left... *)
                  constructor; auto.
                  eapply IHM1; eauto.
              - (* TauL *)
                exfalso; eapply EQ; eauto.
              -
              - (* TauL *)
                pclearbot.
                apply orutt_inv_Vis_r in H.
                destruct H as [[U1 [e1 [k3 [M1 [EV_REL K_RUTT]]]]] | OOM].
                2: {
                  destruct OOM as [o OOM].
                  inv OOM.
                  repeat red in H0.
                  rewrite H0 in H1.
                  setoid_rewrite bind_trigger in H1.
                  setoid_rewrite bind_vis in H1.
                  punfold H1; red in H1; cbn in H1.
                  dependent induction H1.
                  - destruct o.
                    eapply Interp_Memory_PropT_Vis_OOM.
                    rewrite get_inf_tree_equation.
                    cbn.
                    unfold raiseOOM.
                    rewrite bind_trigger.
                    reflexivity.
                  - specialize (EQ t1). contradiction.
                }

                                                         repeat red in H0.
                                                         destruct e; cbn in *.
                                                         + (* ExternalCallE *)
                                                           red in H0.
                                                           setoid_rewrite bind_trigger in H0.
                                                           setoid_rewrite H0 in H1.
                                                           setoid_rewrite bind_vis in H1.
                                                           punfold H1; red in H1; cbn in H1.
                                                           dependent induction H1.
                                                           * { clear IHRUN.
                                                               punfold M1; red in M1; cbn in M1.
                                                               genobs m1 om1.
                                                               clear m1 Heqom1.
                                                               assert (DEC: (exists m1, om1 = TauF m1) \/ (forall m1, om1 <> TauF m1)).
                                                               { destruct om1; eauto; right; red; intros; inversion H. }
                                                               destruct DEC as [EQ' | EQ'].
                                                               { (* Tau case *)
                                                                 destruct EQ' as [m1' EQ'].
                                                                 subst.
                                                                 constructor; auto.
                                                                 right.
                                                                 rewrite (itree_eta_ m1).
                                                                 rewrite (itree_eta_ m3).
                                                                 eapply CIH.

                                                                 pclearbot.
                                                                 punfold H; red in H.
                                                                 pstep. red. cbn.
                                                                 eauto.

                                                                 red.
                                                                 rewrite <- itree_eta_.
                                                                 rewrite <- itree_eta_.

                                                                 rewrite <- tau_eutt.
                                                                 rewrite <- (tau_eutt m3).
                                                                 pstep; red; cbn.
                                                                 auto.
                                                               }

                                                               dependent induction M1.
                                                               - repeat red in EV_REL.
                                                                 destruct e1; repeat destruct s; repeat destruct i; try contradiction.
                                                                 destruct e0, e.
                                                                 destruct EV_REL as (T&F&ARGS); subst.
                                                                 eapply Interp_Memory_PropT_Vis with
                                                                   (k2:=
                                                                      fun '(_, (_, v)) => (get_inf_tree
                                                                                             match DVCInfFin.dvalue_convert_strict v with
                                                                                             | NoOom a => k0 a
                                                                                             | Oom s => raiseOOM s
                                                                                             end)
                                                                   ).
                                                                 + intros a b H H1 H2.
                                                                   destruct b as (?&(?&a')).
                                                                   cbn in *; subst.

                                                                   (*
                         REL0 is k1 to k3...
                         K_RUTT is k3 to k4
                         HK gives k4 to k2
                         REL gives k2 to k0

                         RUN may be useful too... Although, I'm in the
                         middle of dependent induction on RUN, so
                         probably not.
                                                                    *)
                                                                   left.
                                                                   eapply paco2_mon_bot; eauto.

                                                                   specialize (REL0 a').
                                                                   red in REL0.
                                                                   pclearbot.
                                                                   rewrite REL0.



                                                                   inversion RUN.
                                                                   { rewrite itree_eta in HT1.
                                                                     rewrite H4 in HT1.
                                                                     punfold HT1; red in HT1; cbn in HT1.
                                                                     dependent induction HT1.
                                                                   }

                                                                   subst_existT.
                                                                   cbn in H4.
                                                                   red in H4.
                                                                   setoid_rewrite bind_trigger in H4.
                                                                   rewrite H4 in H7.
                                                                   setoid_rewrite bind_vis in H7.
                                                                   setoid_rewrite bind_ret_l in H7.
                                                                   rewrite itree_eta in H7.
                                                                   rewrite H6 in H7.
                                                                   punfold H7; red in H7; cbn in H7.
                                                                   dependent destruction H7.
                                                                   dependent destruction RUN.
                                                                   admit.



                                                                   admit.
                                                                 + cbn. red.
                                                                   setoid_rewrite bind_trigger.
                                                                   reflexivity.
                                                                 + rewrite get_inf_tree_equation.
                                                                   cbn.
                                                                   rewrite bind_vis.
                                                                   pose proof (fin_to_inf_uvalue_refine_strict' _ _ F).
                                                                   rewrite <- H.

                                                                   rewrite Forall2_map_eq with (l2:=args).
                                                                   2: {
                                                                     eapply Forall2_flip.
                                                                     eapply Util.Forall2_impl; [| apply ARGS].
                                                                     intros a b H1.
                                                                     red.
                                                                     symmetry.
                                                                     apply fin_to_inf_dvalue_refine_strict'.
                                                                     auto.
                                                                   }

                                                                   setoid_rewrite bind_ret_l.

                                                                   pstep; red; cbn.
                                                                   constructor.
                                                                   intros v. red.
                                                                   left.
                                                                   apply paco2_eqit_refl.
                                                               - eapply IHRUN.

                                                                 constructor; auto.
                                                             }
                                                           * specialize (EQ t1). contradiction.
                                                         +

                                                           genobs m1 om1.
                                                           clear m1 Heqom1 IHRUN.

                                                           cbn in *.



                                                           repeat red in EV_REL.


                                                           assert (get_inf_tree {| _observe := t2 |} ≈ get_inf_tree (vis (@resum (Type -> Type) IFun OOME
                                                                                                                            (PickUvalueE +' OOME +' UBE +' DebugE +' FailureE)
                                                                                                                            (@ReSum_inr (Type -> Type) IFun sum1 Cat_IFun Inr_sum1 OOME
                                                                                                                               (OOME +' UBE +' DebugE +' FailureE) PickUvalueE
                                                                                                                               (@ReSum_inl (Type -> Type) IFun sum1 Cat_IFun Inl_sum1 OOME OOME
                                                                                                                                  (UBE +' DebugE +' FailureE)
                                                                                                                                  (@ReSum_id (Type -> Type) IFun Id_IFun OOME))) A o) (fun x : A => ITree.bind (ret (s2, (s1, x))) k2))).
                                                           {
                                                             rewrite H1.
                                                             reflexivity.
                                                           }
                                                           rewrite H2.
                                                           eapply get_inf_tree_Proper.
                                                           setoid_rewrite H1.
                                                        }
                                                        punfold H; red in H; cbn in H.
                                                       genobs m1 om1.
                                                       setoid_rewrite (itree_eta_ m1) in IHRUN.
                                                       rewrite <- Heqom1 in IHRUN.
                                                       clear m1 Heqom1.
                                                       dependent induction H.
                                                       + repeat red in H2.
                                                         break_match_hyp.
                                                         * red in H2.
                                                           setoid_rewrite bind_trigger in H2.
                                                           rewrite H2 in H3.
                                                           setoid_rewrite bind_vis in H3.
                                                           setoid_rewrite bind_ret_l in H3.
                                                           inv Heqs.
                                                           repeat red in H.
                                                           destruct e1; try discriminate.
                                                           2: { destruct s. destruct i; try contradiction.
                                                                repeat destruct s; try contradiction.
                                                           }
                                                           destruct e, e0.
                                                           destruct H as (?&?&?); subst.
                                                           eapply Interp_Memory_PropT_Vis.
                                                           2: {
                                                             repeat red.
                                                             setoid_rewrite bind_trigger.
                                                             apply paco2_eqit_refl.
                                                           }
                                                           2: {
                                                             rewrite H3.
                                                             rewrite get_inf_tree_equation.
                                                             cbn.
                                                             rewrite <- bind_ret_r.
                                                             eapply eutt_clo_bind. he

                                                               H5 : DVCInfFin.uvalue_refine_strict f f0

                                                                      eapply eutt_clo_bind with
                                                               (UU:=fun '(ms, (sid, ((lenv, stack), (genv, dv)))) '(ms', (sid', dv')) => ms = ms' /\ sid = sid' /\ dv = dv').
                                                             2: {
                                                               intros u1 u2 H.
                                                               destruct u1 as (ms & (sid' & ((lenv & stack) & (genv & dv)))).
                                                               destruct u2 as (ms' & (sid'' & dv')).
                                                               destruct H as (?&?&?). subst.

                                                               k2 := (fun '(ms, (sid, dv)) => SemNotations.Ret5 genv (lenv, stack) sid ms dv)

                                                                       unfold SemNotations.Ret5.

                                                             }
                                                             (t2 := (observe (vis
                                                                                (subevent E1.DV.dvalue
                                                                                   (E1.ExternalCall t0 (fin_to_inf_uvalue f0) (map fin_to_inf_dvalue args0)))
                                                                                (fun x0 : E1.DV.dvalue =>
                                                                                   get_inf_tree
                                                                                     match DVCInfFin.dvalue_convert_strict x0 with
                                                                                     | NoOom a => k2 (s2, (s1, a))
                                                                                     | Oom s => raiseOOM s
                                                                                     end)))).
                                                             - pstep; red; cbn.
                                                               constructor.
                                                               reflexivity.



                                                               Notation res_L6 := (MemState * (store_id * (local_env * lstack * (global_env * dvalue))))%type.

                                                                 with (ta:=(vis (E1.ExternalCall t0 (fin_to_inf_uvalue f0) (map fin_to_inf_dvalue args0))
                                                                              (fun x0 : E1.DV.dvalue =>
                                                                                 get_inf_tree
                                                                                   match DVCInfFin.dvalue_convert_strict x0 with
                                                                                   | NoOom a => k2 (s2, (s1, a))
                                                                                   | Oom s => raiseOOM s
                                                                                   end))).

                                                                 vis (E1.ExternalCall t0 (fin_to_inf_uvalue f0) (map fin_to_inf_dvalue args0))
                                                                   (fun x0 : E1.DV.dvalue =>
                                                                      get_inf_tree
                                                                        match DVCInfFin.dvalue_convert_strict x0 with
                                                                        | NoOom a => k2 (s2, (s1, a))
                                                                        | Oom s => raiseOOM s
                                                                        end)
                                                                   pstep; red; cbn.
                                                                 constructor.
                                                                 intros v.
                                                                 red.
                                                                 left.
                                                                 cbn.
                                                                 break_match.
                                                                 admit.
                                                             - cbn.
                                                               pose proof (dvalue_convert_strict_safe ).
                                                               reflexivity.
                                                               cbn.
                                                           }
                                                           -- intros a b H H7 H8.
                                                              destruct b as (?&?&?); cbn in *; subst.
                                                              pclearbot.
                                                              left.

                                                              pstep; red; cbn.
                                                              econstructor.
                                                              reflexivity.
                                                              eapply upaco2_mon_bot; eauto.
                                                              eapply H0.
                                                              eauto.
                                                              specialize (H0 a).
                                                              forward H0.

                                                              H0 : forall (a : A0) (b : A),
                                                                  L2_res_refine_strict A0 A e1 a (inl1 e0) b ->
                                                                  upaco2
                                                                    (orutt_ L2_refine_strict L2_res_refine_strict
                                                                       (local_refine_strict × stack_refine_strict
                                                                          × (global_refine_strict × DVCInfFin.dvalue_refine_strict))) bot2
                                                                    (k0 a) (k1 b)



                                                                  - pclearbot.

                                                              do 4 red in H0.
                                                              break_match_hyp.
                                                       + red in H0.
                                                         setoid_rewrite bind_trigger in H0.
                                                         rewrite H0 in H1.
                                                         setoid_rewrite bind_vis in H1.
                                                         punfold H1; red in H1; cbn in H1.
                                                         dependent induction H1.
                                                         * destruct e0.
                                                           rewrite get_inf_tree_equation.
                                                           cbn.
                                                           reflexivity.
                                                           (* TODO: Why won't this evaluate? *)
                                                           admit.
                                                         *
                                                       + red in H0. repeat red in H0.

                                                         cbn in H0.
                                                       - (* TauL *)
                                                         clear IHRUN.
                                                         pclearbot.
                                                         rewrite itree_eta in HT1.
                                                         epose proof orutt_Proper_R2.
                                                         unfold Proper, respectful in H0.
                                                         pose proof H.
                                                         eapply H0 in H1.
                                                         6: {
                                                           symmetry.
                                                           apply HT1.
                                                         }
                                                         all: try reflexivity.
                                                         clear H. rename H1 into H.
                                                         apply orutt_inv_Vis_r in H.
                                                         destruct H.
                                                         2: {
                                                           (* OOM *)
                                                           eapply Interp_Memory_PropT_Vis_OOM.
                                                           destruct H.
                                                           subst.
                                                           cbn in H0.
                                                           red in H0.
                                                           admit.
                                                         }

                                                         destruct H as [U1 [e1 [k3 [M1 [EV_REL K_RUTT]]]]].
                                                         punfold M1.
                                                         red in M1.
                                                         genobs m1 om1.
                                                         clear m1 Heqom1.
                                                         dependent induction M1.
                                                         + (* rename H1 into VIS_HANDLED. *)
                                                           destruct e1.
                                                           cbn in EV_REL; destruct e0; inv EV_REL.
                                                           destruct s. cbn in EV_REL; destruct i; try contradiction.
                                                           destruct s. cbn in EV_REL; destruct m; try contradiction.
                                                           destruct s. cbn in EV_REL; destruct p; try contradiction.
                                                           destruct s.
                                                           2: {
                                                             destruct s. cbn in EV_REL; destruct u; try contradiction.
                                                             destruct s; cbn in EV_REL; try contradiction.
                                                           }

                                                           cbn in *.
                                                           change (VisF (inr1 (inr1 (inr1 (inr1 (inl1 o))))) k0) with (observe (vis (inr1 (inr1 (inr1 (inr1 (inl1 o))))) k0)).
                                                           eapply Interp_Memory_PropT_Vis_OOM with (k1 := k0) (e:=o).
                                                           reflexivity.
                                                         + destruct e, e1;
                                                             cbn in EV_REL.
                                                           destruct e; try contradiction.
                                                           destruct s0; try contradiction.
                                                           destruct i; try contradiction.
                                                           repeat (destruct s0; try contradiction).

                                                           constructor; eauto.
                                                       - (* TauR *)
                                                         specialize (EQ t2).
                                                         contradiction.
                                                       - (* Vis_OOM *)
                                                         pclearbot.
                                                         rewrite itree_eta in HT0.
                                                         punfold H.
                                                         red in H.
                                                         cbn in H.
                                                         inversion H;
                                                           try solve [rewrite <- H1 in HT0; pinversion HT0; try inv CHECK0].
                                                         + rewrite <- H1 in HT0.
                                                           pinversion HT0; subst_existT.
                                                           subst_existT.
                                                           specialize (H4 e0).
                                                           contradiction.
                                                         + rewrite <- H2 in HT0.
                                                           pinversion HT0.
                                                           subst_existT.
                                                           subst_existT.
                                                           Unset Printing Notations.
                                                           Goal (Prop) -> False.
                                                             intros H.
                                                             induction H.

                                                             admit.
                                                             +
                                                               cbn in *.

                                                               subst.

                                                               cbn.
                                                               constructor; eauto.
                                                               eapply IHRUN.

                                                               cbn in *.
                                                               { (* Nondeterminism events *)
                                                                 red in H0.
                                                                 destruct H0.
                                                                 - (* True *)
                                                                   subst.
                                                                   setoid_rewrite bind_ret_l in VIS_HANDLED.

                                                                   specialize (HK true).
                                                                   forward HK. constructor; reflexivity.
                                                                   pclearbot.
                                                                   rewrite <- VIS_HANDLED in HK.

                                                                   eapply Interp_PropT_Vis with (k2 := fun _ => get_nat_tree' {| _observe := observe t2 |}).
                                                                   2: {
                                                                     red.
                                                                     left; auto.
                                                                   }
                                                                   2: {
                                                                     setoid_rewrite bind_ret_l.
                                                                     reflexivity.
                                                                   }

                                                                   intros a RET.
                                                                   eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                                                                   right.
                                                                   rewrite (itree_eta_ (k0 _)).

                                                                   eapply CIH.
                                                                   + specialize (K_RUTT true true).
                                                                     forward K_RUTT; cbn; auto.
                                                                     pclearbot.
                                                                     repeat rewrite <- itree_eta_.
                                                                     assert (k0 true ≈ k3 true) as K0K3 by apply REL.
                                                                     rewrite K0K3.
                                                                     punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.
                                                                     pstep; red; cbn; eauto.
                                                                   + repeat rewrite <- itree_eta_.
                                                                     eapply HK.
                                                                 - (* False *)
                                                                   subst.
                                                                   setoid_rewrite bind_ret_l in VIS_HANDLED.

                                                                   specialize (HK false).
                                                                   forward HK. constructor; reflexivity.
                                                                   pclearbot.
                                                                   rewrite <- VIS_HANDLED in HK.

                                                                   eapply Interp_PropT_Vis with (k2 := fun _ => get_nat_tree' {| _observe := observe t2 |}).
                                                                   2: {
                                                                     red.
                                                                     right; auto.
                                                                   }
                                                                   2: {
                                                                     setoid_rewrite bind_ret_l.
                                                                     reflexivity.
                                                                   }

                                                                   intros a RET.
                                                                   eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                                                                   right.
                                                                   rewrite (itree_eta_ (k0 _)).

                                                                   eapply CIH.
                                                                   + specialize (K_RUTT false false).
                                                                     forward K_RUTT; cbn; auto.
                                                                     pclearbot.
                                                                     repeat rewrite <- itree_eta_.
                                                                     assert (k0 false ≈ k3 false) as K0K3 by apply REL.
                                                                     rewrite K0K3.

                                                                     punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.
                                                                     pstep; red; cbn; eauto.
                                                                   + repeat rewrite <- itree_eta_.
                                                                     eapply HK.
                                                               }

                                                               { (* Regular events *)
                                                                 destruct b.
                                                                 red in H0.
                                                                 rewrite H0 in VIS_HANDLED.

                                                                 setoid_rewrite bind_trigger in VIS_HANDLED.
                                                                 punfold VIS_HANDLED. red in VIS_HANDLED.
                                                                 cbn in VIS_HANDLED.
                                                                 dependent induction VIS_HANDLED.
                                                                 { rewrite <- x.

                                                                   eapply Interp_PropT_Vis with (k2:=(fun n0 : nat =>
                                                                                                        get_nat_tree' (k2 (if Nat.eqb n0 0 then false else if Nat.eqb n0 1 then true else false)))).
                                                                   2: {
                                                                     red.
                                                                     reflexivity.
                                                                   }
                                                                   2: {
                                                                     cbn.
                                                                     setoid_rewrite bind_trigger.
                                                                     pstep; red; cbn.

                                                                     destruct EV_REL as [[R1 R3] | [R1 R3]]; subst; auto.
                                                                     - constructor.
                                                                       intros v.
                                                                       red.
                                                                       specialize (REL0 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false)).
                                                                       red in REL0.
                                                                       pclearbot.
                                                                       assert (k5 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false) ≈ k2 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false)) as K0K2.
                                                                       { eapply REL0.
                                                                       }

                                                                       setoid_rewrite H0 in HK.

                                                                       destruct v; [| destruct v]; cbn in *.
                                                                       + repeat (rewrite <- itree_eta_).
                                                                         specialize (HK false).
                                                                         forward HK.
                                                                         { eapply ReturnsVis.
                                                                           unfold ITree.trigger.
                                                                           reflexivity.
                                                                           constructor. reflexivity.
                                                                         }
                                                                         pclearbot.
                                                                         left.
                                                                         setoid_rewrite K0K2.
                                                                         assert ((get_nat_tree' (k2 false)) ≈ (get_nat_tree' (k2 false))).
                                                                         reflexivity.
                                                                         eauto.
                                                                       + repeat (rewrite <- itree_eta_).
                                                                         specialize (HK true).
                                                                         forward HK.
                                                                         { eapply ReturnsVis.
                                                                           unfold ITree.trigger.
                                                                           reflexivity.
                                                                           constructor. reflexivity.
                                                                         }
                                                                         pclearbot.
                                                                         left.
                                                                         setoid_rewrite K0K2.
                                                                         assert ((get_nat_tree' (k2 true)) ≈ (get_nat_tree' (k2 true))).
                                                                         reflexivity.
                                                                         eauto.
                                                                       + (* Bogus case *)
                                                                         repeat (rewrite <- itree_eta_).
                                                                         specialize (HK false).
                                                                         forward HK.
                                                                         { eapply ReturnsVis.
                                                                           unfold ITree.trigger.
                                                                           reflexivity.
                                                                           constructor. reflexivity.
                                                                         }
                                                                         pclearbot.
                                                                         left.
                                                                         setoid_rewrite K0K2.
                                                                         assert ((get_nat_tree' (k2 false)) ≈ (get_nat_tree' (k2 false))).
                                                                         reflexivity.
                                                                         eauto.
                                                                     - constructor.
                                                                       intros v.
                                                                       red.
                                                                       specialize (REL0 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false)).
                                                                       red in REL0.
                                                                       pclearbot.
                                                                       assert (k5 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false) ≈ k2 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false)) as K0K2.
                                                                       { eapply REL0.
                                                                       }

                                                                       setoid_rewrite H0 in HK.

                                                                       destruct v; [| destruct v]; cbn in *.
                                                                       + repeat (rewrite <- itree_eta_).
                                                                         specialize (HK false).
                                                                         forward HK.
                                                                         { eapply ReturnsVis.
                                                                           unfold ITree.trigger.
                                                                           reflexivity.
                                                                           constructor. reflexivity.
                                                                         }
                                                                         pclearbot.
                                                                         left.
                                                                         setoid_rewrite K0K2.
                                                                         assert ((get_nat_tree' (k2 false)) ≈ (get_nat_tree' (k2 false))).
                                                                         reflexivity.
                                                                         eauto.
                                                                       + repeat (rewrite <- itree_eta_).
                                                                         specialize (HK true).
                                                                         forward HK.
                                                                         { eapply ReturnsVis.
                                                                           unfold ITree.trigger.
                                                                           reflexivity.
                                                                           constructor. reflexivity.
                                                                         }
                                                                         pclearbot.
                                                                         left.
                                                                         setoid_rewrite K0K2.
                                                                         assert ((get_nat_tree' (k2 true)) ≈ (get_nat_tree' (k2 true))).
                                                                         reflexivity.
                                                                         eauto.
                                                                       + (* Bogus case *)
                                                                         repeat (rewrite <- itree_eta_).
                                                                         specialize (HK false).
                                                                         forward HK.
                                                                         { eapply ReturnsVis.
                                                                           unfold ITree.trigger.
                                                                           reflexivity.
                                                                           constructor. reflexivity.
                                                                         }
                                                                         pclearbot.
                                                                         left.
                                                                         setoid_rewrite K0K2.
                                                                         assert ((get_nat_tree' (k2 false)) ≈ (get_nat_tree' (k2 false))).
                                                                         reflexivity.
                                                                         eauto.
                                                                   }

                                                                   intros a RET.
                                                                   specialize (K_RUTT a (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false)).
                                                                   forward K_RUTT.
                                                                   cbn; auto.

                                                                   specialize (HK (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false)).
                                                                   rewrite H0 in HK.
                                                                   forward HK.
                                                                   { eapply ReturnsVis.
                                                                     unfold ITree.trigger.
                                                                     reflexivity.
                                                                     cbn.
                                                                     constructor.
                                                                     reflexivity.
                                                                   }

                                                                   right.
                                                                   rewrite (itree_eta_ (k0 a)).
                                                                   rewrite (itree_eta_ (k2 _)).
                                                                   pclearbot.
                                                                   eapply CIH;
                                                                     repeat rewrite <- itree_eta_.

                                                                   repeat rewrite <- itree_eta_.
                                                                   assert (k0 a ≈ k3 a) as K0K3 by apply REL.
                                                                   rewrite K0K3.
                                                                   eapply K_RUTT.
                                                                   red.
                                                                   eapply HK.
                                                                 }

                                                                 { rewrite <- x in EQ.
                                                                   specialize (EQ t1).
                                                                   contradiction.
                                                                 }
                                                               }
                                                             + constructor; auto.
                                                               eapply IHM1; eauto.
                                                             - rewrite <- x in EQ.
                                                               exfalso.
                                                               eapply EQ; eauto.
                                                             }
                                                             + pstep; red; cbn.
                                                               constructor.
                                                               right.
                                                               rewrite (itree_eta_ m1).
                                                               rewrite (itree_eta_ t2).

                                                               pclearbot.
                                                               eapply CIH; repeat rewrite <- itree_eta_.
                                                               eauto.

                                                               red.
                                                               rewrite <- (tau_eutt m2).

                                                               pstep; red; cbn.
                                                               auto.
                                                             - subst.
                                                               apply interp_memory_prop_inv_tau_l in RUN.
                                                               pclearbot.

                                                               pstep; red; constructor; auto.
                                                               pclearbot.

                                                               punfold RUN. red in RUN.



                                                               apply interp_memory_prop _tau_inv in RUN.
                                                               destruct RUN as [r3 [REQ EQ]]; subst.

                                                               inversion REQ; cbn in *.

                                                               red.
                                                               red.

                                                               (* TODO: Move these *)
                                                               Lemma local_env_refine_lift :
                                                                 forall lenv l,
                                                                   local_refine_strict lenv l ->
                                                                   lenv = lift_local_env l.
                                                               Proof.
                                                                 induction lenv, l; intros LR; auto.
                                                                 - apply alist_refine_nil_cons_inv in LR.
                                                                   contradiction.
                                                                 - apply alist_refine_cons_nil_inv in LR.
                                                                   contradiction.
                                                                 - red in LR.
                                                                   red in LR.
                                                                   cbn in LR.
                                                                   unfold OptionUtil.option_rel2 in LR.
                                                                   cbn in *.
                                                                   destruct p, a.
                                                                   cbn.
                                                               Qed.

                                                               destruct H as [[R1 R3] | [R1 R3]]; subst; auto.
                                                             - punfold RUN.
                                                               red in RUN.
                                                               cbn in RUN.

                                                               assert (DEC: (exists m3, ot_bool2 = TauF m3) \/ (forall m3, ot_bool2 <> TauF m3)).
                                                               { destruct ot_bool2; eauto; right; red; intros; inversion H0. }

                                                               destruct DEC as [EQ | EQ].
                                                               { destruct EQ as [m3 EQ].
                                                                 subst.
                                                                 pstep; red; cbn.
                                                                 constructor.
                                                                 right.
                                                                 rewrite (itree_eta_ m1).
                                                                 rewrite (itree_eta_ m3).
                                                                 eapply CIH.

                                                                 pclearbot.
                                                                 punfold H; red in H.
                                                                 pstep. red. cbn.
                                                                 eauto.

                                                                 red.
                                                                 rewrite <- itree_eta_.
                                                                 rewrite <- itree_eta_.

                                                                 rewrite <- tau_eutt.
                                                                 rewrite <- (tau_eutt m3).
                                                                 pstep; red; cbn.
                                                                 auto.
                                                               }

                                                               inversion RUN; subst.
                                                               + specialize (EQ t2).
                                                                 contradiction.
                                                               + pstep; red; cbn.
                                                                 constructor; auto.

                                                                 rewrite (itree_eta_ m2) in H.
                                                                 rewrite (itree_eta_ m2) in RUN.
                                                                 genobs m2 om2.
                                                                 setoid_rewrite <- Heqom2 in HS.
                                                                 clear Heqom2.
                                                                 clear m2.
                                                                 induction HS; subst.
                                                                 -- inversion RUN; subst.
                                                                    cbn in *.
                                                                    inversion HS; subst.

                                                                    pclearbot.
                                                                    punfold H.
                                                                    red in H.

                                                                    { dependent induction H.
                                                                      - rewrite <- x.
                                                                        constructor.
                                                                        destruct H as [[R1 R3] | [R1 R3]]; subst; auto.
                                                                      - rewrite <- x.
                                                                        constructor; auto.
                                                                    }
                                                                 -- specialize (EQ t2).
                                                                    contradiction.
                                                                 -- eapply IHHS; eauto.
                                                                    left.
                                                                    pclearbot.
                                                                    assert (rutt (@top_level_rel) (@top_level_rel_ans) nb  m1 (Tau t1)).
                                                                    { apply H.
                                                                    }
                                                                    setoid_rewrite tau_eutt in H0.
                                                                    rewrite <- itree_eta_.
                                                                    apply H0.
                                                                 -- specialize (EQ t2).
                                                                    contradiction.
                                                                 -- { dependent induction RUN; subst.
                                                                      - rewrite <- x in EQ.
                                                                        specialize (EQ t0).
                                                                        contradiction.
                                                                      - (* TauL *)
                                                                        clear IHRUN.
                                                                        pclearbot.

                                                                        apply rutt_inv_Vis_r in H.
                                                                        destruct H as [U1 [e1 [k3 [M1 [EV_REL K_RUTT]]]]].
                                                                        punfold M1.
                                                                        red in M1.
                                                                        genobs m1 om1.
                                                                        clear m1 Heqom1.
                                                                        dependent induction M1.
                                                                        + rename H1 into VIS_HANDLED.
                                                                          destruct e, e1; try destruct n; try destruct n0; cbn in EV_REL; try inversion EV_REL.

                                                                          { (* Nondeterminism events *)
                                                                            red in H0.
                                                                            destruct H0.
                                                                            - (* True *)
                                                                              subst.
                                                                              setoid_rewrite bind_ret_l in VIS_HANDLED.

                                                                              specialize (HK true).
                                                                              forward HK. constructor; reflexivity.
                                                                              pclearbot.
                                                                              rewrite <- VIS_HANDLED in HK.

                                                                              eapply Interp_PropT_Vis with (k2 := fun _ => get_nat_tree' {| _observe := observe t2 |}).
                                                                              2: {
                                                                                red.
                                                                                left; auto.
                                                                              }
                                                                              2: {
                                                                                setoid_rewrite bind_ret_l.
                                                                                reflexivity.
                                                                              }

                                                                              intros a RET.
                                                                              eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                                                                              right.
                                                                              rewrite (itree_eta_ (k0 _)).

                                                                              eapply CIH.
                                                                              + specialize (K_RUTT true true).
                                                                                forward K_RUTT; cbn; auto.
                                                                                pclearbot.
                                                                                repeat rewrite <- itree_eta_.
                                                                                assert (k0 true ≈ k3 true) as K0K3 by apply REL.
                                                                                rewrite K0K3.
                                                                                punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.
                                                                                pstep; red; cbn; eauto.
                                                                              + repeat rewrite <- itree_eta_.
                                                                                eapply HK.
                                                                            - (* False *)
                                                                              subst.
                                                                              setoid_rewrite bind_ret_l in VIS_HANDLED.

                                                                              specialize (HK false).
                                                                              forward HK. constructor; reflexivity.
                                                                              pclearbot.
                                                                              rewrite <- VIS_HANDLED in HK.

                                                                              eapply Interp_PropT_Vis with (k2 := fun _ => get_nat_tree' {| _observe := observe t2 |}).
                                                                              2: {
                                                                                red.
                                                                                right; auto.
                                                                              }
                                                                              2: {
                                                                                setoid_rewrite bind_ret_l.
                                                                                reflexivity.
                                                                              }

                                                                              intros a RET.
                                                                              eapply Returns_Ret_ in RET; [| reflexivity]; subst.

                                                                              right.
                                                                              rewrite (itree_eta_ (k0 _)).

                                                                              eapply CIH.
                                                                              + specialize (K_RUTT false false).
                                                                                forward K_RUTT; cbn; auto.
                                                                                pclearbot.
                                                                                repeat rewrite <- itree_eta_.
                                                                                assert (k0 false ≈ k3 false) as K0K3 by apply REL.
                                                                                rewrite K0K3.

                                                                                punfold K_RUTT. red in K_RUTT. cbn in K_RUTT.
                                                                                pstep; red; cbn; eauto.
                                                                              + repeat rewrite <- itree_eta_.
                                                                                eapply HK.
                                                                          }

                                                                          { (* Regular events *)
                                                                            destruct b.
                                                                            red in H0.
                                                                            rewrite H0 in VIS_HANDLED.

                                                                            setoid_rewrite bind_trigger in VIS_HANDLED.
                                                                            punfold VIS_HANDLED. red in VIS_HANDLED.
                                                                            cbn in VIS_HANDLED.
                                                                            dependent induction VIS_HANDLED.
                                                                            { rewrite <- x.

                                                                              eapply Interp_PropT_Vis with (k2:=(fun n0 : nat =>
                                                                                                                   get_nat_tree' (k2 (if Nat.eqb n0 0 then false else if Nat.eqb n0 1 then true else false)))).
                                                                              2: {
                                                                                red.
                                                                                reflexivity.
                                                                              }
                                                                              2: {
                                                                                cbn.
                                                                                setoid_rewrite bind_trigger.
                                                                                pstep; red; cbn.

                                                                                destruct EV_REL as [[R1 R3] | [R1 R3]]; subst; auto.
                                                                                - constructor.
                                                                                  intros v.
                                                                                  red.
                                                                                  specialize (REL0 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false)).
                                                                                  red in REL0.
                                                                                  pclearbot.
                                                                                  assert (k5 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false) ≈ k2 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false)) as K0K2.
                                                                                  { eapply REL0.
                                                                                  }

                                                                                  setoid_rewrite H0 in HK.

                                                                                  destruct v; [| destruct v]; cbn in *.
                                                                                  + repeat (rewrite <- itree_eta_).
                                                                                    specialize (HK false).
                                                                                    forward HK.
                                                                                    { eapply ReturnsVis.
                                                                                      unfold ITree.trigger.
                                                                                      reflexivity.
                                                                                      constructor. reflexivity.
                                                                                    }
                                                                                    pclearbot.
                                                                                    left.
                                                                                    setoid_rewrite K0K2.
                                                                                    assert ((get_nat_tree' (k2 false)) ≈ (get_nat_tree' (k2 false))).
                                                                                    reflexivity.
                                                                                    eauto.
                                                                                  + repeat (rewrite <- itree_eta_).
                                                                                    specialize (HK true).
                                                                                    forward HK.
                                                                                    { eapply ReturnsVis.
                                                                                      unfold ITree.trigger.
                                                                                      reflexivity.
                                                                                      constructor. reflexivity.
                                                                                    }
                                                                                    pclearbot.
                                                                                    left.
                                                                                    setoid_rewrite K0K2.
                                                                                    assert ((get_nat_tree' (k2 true)) ≈ (get_nat_tree' (k2 true))).
                                                                                    reflexivity.
                                                                                    eauto.
                                                                                  + (* Bogus case *)
                                                                                    repeat (rewrite <- itree_eta_).
                                                                                    specialize (HK false).
                                                                                    forward HK.
                                                                                    { eapply ReturnsVis.
                                                                                      unfold ITree.trigger.
                                                                                      reflexivity.
                                                                                      constructor. reflexivity.
                                                                                    }
                                                                                    pclearbot.
                                                                                    left.
                                                                                    setoid_rewrite K0K2.
                                                                                    assert ((get_nat_tree' (k2 false)) ≈ (get_nat_tree' (k2 false))).
                                                                                    reflexivity.
                                                                                    eauto.
                                                                                - constructor.
                                                                                  intros v.
                                                                                  red.
                                                                                  specialize (REL0 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false)).
                                                                                  red in REL0.
                                                                                  pclearbot.
                                                                                  assert (k5 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false) ≈ k2 (if Nat.eqb v 0 then false else if Nat.eqb v 1 then true else false)) as K0K2.
                                                                                  { eapply REL0.
                                                                                  }

                                                                                  setoid_rewrite H0 in HK.

                                                                                  destruct v; [| destruct v]; cbn in *.
                                                                                  + repeat (rewrite <- itree_eta_).
                                                                                    specialize (HK false).
                                                                                    forward HK.
                                                                                    { eapply ReturnsVis.
                                                                                      unfold ITree.trigger.
                                                                                      reflexivity.
                                                                                      constructor. reflexivity.
                                                                                    }
                                                                                    pclearbot.
                                                                                    left.
                                                                                    setoid_rewrite K0K2.
                                                                                    assert ((get_nat_tree' (k2 false)) ≈ (get_nat_tree' (k2 false))).
                                                                                    reflexivity.
                                                                                    eauto.
                                                                                  + repeat (rewrite <- itree_eta_).
                                                                                    specialize (HK true).
                                                                                    forward HK.
                                                                                    { eapply ReturnsVis.
                                                                                      unfold ITree.trigger.
                                                                                      reflexivity.
                                                                                      constructor. reflexivity.
                                                                                    }
                                                                                    pclearbot.
                                                                                    left.
                                                                                    setoid_rewrite K0K2.
                                                                                    assert ((get_nat_tree' (k2 true)) ≈ (get_nat_tree' (k2 true))).
                                                                                    reflexivity.
                                                                                    eauto.
                                                                                  + (* Bogus case *)
                                                                                    repeat (rewrite <- itree_eta_).
                                                                                    specialize (HK false).
                                                                                    forward HK.
                                                                                    { eapply ReturnsVis.
                                                                                      unfold ITree.trigger.
                                                                                      reflexivity.
                                                                                      constructor. reflexivity.
                                                                                    }
                                                                                    pclearbot.
                                                                                    left.
                                                                                    setoid_rewrite K0K2.
                                                                                    assert ((get_nat_tree' (k2 false)) ≈ (get_nat_tree' (k2 false))).
                                                                                    reflexivity.
                                                                                    eauto.
                                                                              }

                                                                              intros a RET.
                                                                              specialize (K_RUTT a (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false)).
                                                                              forward K_RUTT.
                                                                              cbn; auto.

                                                                              specialize (HK (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false)).
                                                                              rewrite H0 in HK.
                                                                              forward HK.
                                                                              { eapply ReturnsVis.
                                                                                unfold ITree.trigger.
                                                                                reflexivity.
                                                                                cbn.
                                                                                constructor.
                                                                                reflexivity.
                                                                              }

                                                                              right.
                                                                              rewrite (itree_eta_ (k0 a)).
                                                                              rewrite (itree_eta_ (k2 _)).
                                                                              pclearbot.
                                                                              eapply CIH;
                                                                                repeat rewrite <- itree_eta_.

                                                                              repeat rewrite <- itree_eta_.
                                                                              assert (k0 a ≈ k3 a) as K0K3 by apply REL.
                                                                              rewrite K0K3.
                                                                              eapply K_RUTT.
                                                                              red.
                                                                              eapply HK.
                                                                            }

                                                                            { rewrite <- x in EQ.
                                                                              specialize (EQ t1).
                                                                              contradiction.
                                                                            }
                                                                          }
                                                                        + constructor; auto.
                                                                          eapply IHM1; eauto.
                                                                      - rewrite <- x in EQ.
                                                                        exfalso.
                                                                        eapply EQ; eauto.
                                                                    }
                                                               + pstep; red; cbn.
                                                                 constructor.
                                                                 right.
                                                                 rewrite (itree_eta_ m1).
                                                                 rewrite (itree_eta_ t2).

                                                                 pclearbot.
                                                                 eapply CIH; repeat rewrite <- itree_eta_.
                                                                 eauto.

                                                                 red.
                                                                 rewrite <- (tau_eutt m2).

                                                                 pstep; red; cbn.
                                                                 auto.
                                                             - rename H into EV_REL.
                                                               destruct e1, e2; try destruct n; try destruct n0; cbn in EV_REL; try inversion EV_REL.
                                                               rename H0 into K_RUTT.
                                                               subst.

                                                               + (* NonDet events *)
                                                                 punfold RUN. red in RUN.
                                                                 cbn in RUN.
                                                                 dependent induction RUN.
                                                                 -- pstep; red; cbn.
                                                                    constructor; auto.
                                                                    rewrite (itree_eta_ t2).

                                                                    forward IHRUN; auto.
                                                                    specialize (IHRUN k2).
                                                                    forward IHRUN; auto.
                                                                    forward IHRUN; auto.
                                                                    punfold IHRUN.
                                                                 --
                                                                   red in H.
                                                                   { destruct H; subst; setoid_rewrite bind_ret_l in H0.
                                                                     - pstep; red; cbn.

                                                                       eapply Interp_PropT_Vis with (k2 := fun _ => get_nat_tree' {| _observe := observe t2 |}).
                                                                       2: {
                                                                         left. reflexivity.
                                                                       }
                                                                       2: {
                                                                         setoid_rewrite bind_ret_l.
                                                                         reflexivity.
                                                                       }

                                                                       intros a RET.
                                                                       eapply Returns_Ret_ in RET; [| reflexivity]; subst.
                                                                       right.

                                                                       rewrite (itree_eta_ (k1 true)).
                                                                       eapply CIH; repeat rewrite <- itree_eta_.
                                                                       + specialize (K_RUTT true true).
                                                                         forward K_RUTT; cbn; auto.
                                                                         pclearbot.
                                                                         apply K_RUTT.
                                                                       + rewrite H0.
                                                                         specialize (HK true).
                                                                         forward HK.
                                                                         constructor; reflexivity.
                                                                         pclearbot.
                                                                         apply HK.
                                                                     - pstep; red; cbn.

                                                                       eapply Interp_PropT_Vis with (k2 := fun _ => get_nat_tree' {| _observe := observe t2 |}).
                                                                       2: {
                                                                         right. reflexivity.
                                                                       }
                                                                       2: {
                                                                         setoid_rewrite bind_ret_l.
                                                                         reflexivity.
                                                                       }

                                                                       intros a RET.
                                                                       eapply Returns_Ret_ in RET; [| reflexivity]; subst.
                                                                       right.

                                                                       rewrite (itree_eta_ (k1 false)).
                                                                       eapply CIH; repeat rewrite <- itree_eta_.
                                                                       + specialize (K_RUTT false false).
                                                                         forward K_RUTT; cbn; auto.
                                                                         pclearbot.
                                                                         apply K_RUTT.
                                                                       + rewrite H0.
                                                                         specialize (HK false).
                                                                         forward HK.
                                                                         constructor; reflexivity.
                                                                         pclearbot.
                                                                         apply HK.
                                                                   }
                                                               + { (* Regular events *)
                                                                   destruct b.
                                                                   rename EV_REL into NB.
                                                                   subst.
                                                                   punfold RUN. red in RUN. cbn in RUN.

                                                                   dependent induction RUN.
                                                                   - pstep; red; cbn.
                                                                     constructor; auto.

                                                                     forward IHRUN; auto.
                                                                     specialize (IHRUN _ k2 NB).
                                                                     forward IHRUN; auto.
                                                                     forward IHRUN; auto.
                                                                     punfold IHRUN.
                                                                   - red in H.
                                                                     rewrite H in H1.
                                                                     rename H0 into K_RUTT.

                                                                     setoid_rewrite bind_trigger in H1.
                                                                     punfold H1; red in H1; cbn in H1.
                                                                     dependent induction H1.
                                                                     { rewrite <- x.
                                                                       pstep; red; cbn.
                                                                       assert ((VisF (nat_ev (if b then 1 else 0))
                                                                                  (fun n0 : nat =>
                                                                                     get_nat_tree'
                                                                                       (if Nat.eqb n0 0
                                                                                        then k0 false
                                                                                        else if Nat.eqb n0 1 then k0 true else k0 false))) = observe (Vis (nat_ev (if b then 1 else 0))
                                                                                                                                                        (fun n0 : nat =>
                                                                                                                                                           get_nat_tree'
                                                                                                                                                             (if Nat.eqb n0 0
                                                                                                                                                              then k0 false
                                                                                                                                                              else if Nat.eqb n0 1 then k0 true else k0 false)))) as VIS by auto.

                                                                       rewrite VIS.
                                                                       clear VIS.
                                                                       { eapply Interp_PropT_Vis with (k2:=(fun n0 : nat =>
                                                                                                              get_nat_tree'
                                                                                                                (if Nat.eqb n0 0
                                                                                                                 then k0 false
                                                                                                                 else if Nat.eqb n0 1 then k0 true else k0 false))).
                                                                         2: {
                                                                           red.
                                                                           reflexivity.
                                                                         }
                                                                         2: {
                                                                           setoid_rewrite bind_trigger.
                                                                           destruct NB as [[R1 R3] | [R1 R3]]; subst; auto;
                                                                             reflexivity.
                                                                         }

                                                                         intros a RET.
                                                                         right.
                                                                         rewrite (itree_eta_ (k1 _)).
                                                                         rewrite (itree_eta_ (if Nat.eqb a 0 then _ else _)).
                                                                         eapply CIH; repeat rewrite <- itree_eta_.

                                                                         specialize (K_RUTT a (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false)).
                                                                         forward K_RUTT; cbn; auto.
                                                                         pclearbot.
                                                                         apply K_RUTT.

                                                                         setoid_rewrite H in HK.
                                                                         specialize (HK (if Nat.eqb a 0 then false else if Nat.eqb a 1 then true else false)).

                                                                         destruct a; [| destruct a]; cbn in *.
                                                                         - forward HK.
                                                                           { eapply ReturnsVis.
                                                                             unfold ITree.trigger.
                                                                             reflexivity.
                                                                             constructor. reflexivity.
                                                                           }
                                                                           pclearbot.
                                                                           assert (k0 false ≈ k3 false) as K0K3 by apply REL.
                                                                           rewrite K0K3.
                                                                           eapply HK.
                                                                         - repeat (rewrite <- itree_eta_).
                                                                           forward HK.
                                                                           { eapply ReturnsVis.
                                                                             unfold ITree.trigger.
                                                                             reflexivity.
                                                                             constructor. reflexivity.
                                                                           }
                                                                           pclearbot.
                                                                           assert (k0 true ≈ k3 true) as K0K3 by apply REL.
                                                                           setoid_rewrite K0K3.
                                                                           eapply HK.
                                                                         - (* Bogus case *)
                                                                           repeat (rewrite <- itree_eta_).
                                                                           forward HK.
                                                                           { eapply ReturnsVis.
                                                                             unfold ITree.trigger.
                                                                             reflexivity.
                                                                             constructor. reflexivity.
                                                                           }
                                                                           pclearbot.
                                                                           assert (k0 false ≈ k3 false) as K0K3 by apply REL.
                                                                           setoid_rewrite K0K3.
                                                                           eapply HK.
                                                                       }
                                                                     }

                                                                     { rewrite <- x.
                                                                       pstep; red; cbn.
                                                                       constructor; auto.

                                                                       specialize (IHeqitF b k3 t1 HK H eq_refl eq_refl).
                                                                       forward IHeqitF; auto.
                                                                       forward IHeqitF; auto.
                                                                       forward IHeqitF; auto.

                                                                       punfold IHeqitF.
                                                                     }
                                                                 }
                                                             - pstep; red; cbn.
                                                               constructor; auto.
                                                               forward IHREL; auto.
                                                               forward IHREL; auto.

                                                               punfold IHREL.
                                                             - eapply IHREL; eauto.
                                                               red in RUN.
                                                               setoid_rewrite tau_eutt in RUN.
                                                               rewrite <- itree_eta_.
                                                               apply RUN.
                                                             }
                                                             admit.

                                                             { apply get_inf_tree_rutt.
                                                             }
                                                           Qed.


                                                           assert (itree InfLP.Events.L3 TopLevelBigIntptr.res_L6).



                                                           { revert FIN_HANDLED.
                                                             revert REL.
                                                             revert t_inf t_fin t_fin2.
                                                             cofix CIH.

                                                             intros t_inf t_fin t_fin2 REL FIN_HANDLED.
                                                             apply orutt_inv_Type in REL.
                                                             destruct REL.
                                                             destruct s as [[[[[RET | TAU] | VIS] | VISOOM] | TauL] | TauR].
                                                             - (* Ret *)
                                                               destruct RET as (r1 & r2 & (RRr1r2 & RET1) & RET2).
                                                               admit.
                                                             - (* TauR *)
                                                               exfalso.
                                                               red in REL.
                                                               pinversion REL.
                                                               admit.
                                                               admit.
                                                               admit.
                                                               admit.
                                                               admit.

                                                               +
                                                                 (* Double tau *)
                                                                 (exists t1' t2', (paco2 (interp_PropT_ h_spec RR true true (OOME:=OOME)) bot2 t1' t2') * (TauF t1' = observe t1) * (TauF t2' = observe t2)) +
                                                                   (* Tau left *)
                                                                   (exists t1' t2',
                                                                       (interp_PropTF (OOME:=OOME) h_spec RR true true (upaco2 (interp_PropT_ h_spec RR true true (OOME:=OOME)) bot2) (observe t1') (observe t2)) *
                                                                         (TauF t1' = observe t1) * (t2' = observe t2)) +
                                                                   (* Tau right *)
                                                                   (exists t1' t2',
                                                                       (interp_PropTF (OOME:=OOME) h_spec RR true true (upaco2 (interp_PropT_ h_spec RR true true (OOME:=OOME)) bot2) (observe t1) (observe t2')) *
                                                                         (t1' = observe t1) * (TauF t2' = observe t2)) +
                                                                   (* OOM vis *)
                                                                   (exists (A : Type) (e : OOM A) k1 t1' t2',
                                                                       (t1' ≅ vis e k1) * (observe t1' = observe t1) * (t2' = observe t2)) +
                                                                   (* Vis nodes *)
                                                                   (exists (A : Type) e k1 k2 ta t2',
                                                                       (forall (a : A), Returns a ta -> upaco2 (interp_PropT_ h_spec RR true true (OOME:=OOME)) bot2 (k1 a) (k2 a)) *
                                                                         (h_spec A e ta) *
                                                                         (t2' ≈ x <- ta;; k2 x) *
                                                                         (VisF e k1 = observe t1) *
                                                                         (observe t2' = observe t2))
                                                           )
                                                       )%type.
                                                        Admitted.

                                                        apply interp_prop_inv_Type in REL.
                                                        pinversion REL.

                                                        }

                                                        punfold RL2.
                                                        red in RL2.
                                                        punfold H.
                                                        red in H.


                                                        Definition convert_tree (t : itree L3 (FinMem.MMEP.MMSP.MemState * (MemPropT.store_id * (local_env * @stack local_env * res_L1)))) : itree InfLP.Events.L3 TopLevelBigIntptr.res_L6.
                                                        Proof.
                                                          revert t.
                                                          cofix CIH.
                                                          intros t.
                                                          destruct t.
                                                          rename _observe into t.
                                                          constructor.
                                                          induction t.
                                                          - (* Ret *)
                                                            destruct r as [ms [sid [[lenv s] [genv dv]]]].
                                                            apply RetF.
                                                            (* Convert the finite values to infinite ones*)
                                                            constructor; [|constructor; [| constructor; [| constructor]]].
                                                            + (* MemState conversion *)
                                                              admit.
                                                            + exact sid.
                                                            + (* Locals and local stack *)
                                                              admit.
                                                            + (* Global environment *)
                                                              admit.
                                                            + pose proof DVC2.dvalue_convert_strict.
                                                              specialize (H dv).
                                                              (* I *should* know that converting a finite dvalue to an
            infinite dvalue always succeeds *)
                                                              destruct H.
                                                              -- exact d.
                                                              -- (* OOM here should be a contradiction... *)
                                                                admit.
                                                          - (* Tau *)
                                                            apply TauF.
                                                            specialize (CIH t).
                                                            apply CIH.
                                                          - (* Vis *)
                                                            apply VisF with (X:=X).
                                                            + (* Result from handler *)
                                                              (* We actually already have event conversions... *)
                                                              pose proof (EC2.L3_convert_strict _ e).
                                                              (* Actually the event conversion we have gives us a new itree... *)
                                                              destruct e.
                                                              -- (* ExternalCallE *)
                                                                inv e.
                                                                constructor.

                                                                admit.
                                                            + intros x.
                                                              specialize (k x).
                                                              apply CIH. apply k.
                                                              Guarded.
                                                              punfold t.
                                                        Defined.

                                                        (* I need to find a `t` that corresponds to the `t'` that's in the
       set given by the interpretation of memory events in `t2`...

       I guess I need to know what decisions were made to get `t'` out
       of `t2`, and make similar decisions to get `t` out of `t1`.

       I guess we need to do coinduction on `t2`?

       - Whenever we have a `Ret` `t'` is should going to end up being
         basically the same `Ret`...
       - Tau nodes should basically be irrelevant...
       - Vis nodes have two cases...
         1. The vis node is an event that isn't interpreted by the
            memory handler... No non-determinism in this, so the
            corresponding `t` should just raise the same event again.
         2. The vis node is a memory event...

       In the second case where the vis is a memory event that we
       interpret we can have non-determinism. E.g., we might have an
       Alloca event, and we will have to pick the location in memory
       that the block gets allocated. `t'` can be any tree where a
       valid address for the allocated block is returned... So, we'll
       need to show that any valid address to allocate a block in the
       current state of the finite memory corresponds to a valid
       address to allocate a block in the current state of the
       corresponding infinite memory. This should hopefully not be too
       bad because the infinite and finite memories will have the same
       layout (this assumption is missing from the initial draft
       of this lemma).
                                                         *)

                                                        (*   unfold IS1.MEM.MEM_SPEC_INTERP.interp_memory_prop. *)
                                                        (*   unfold IS2.MEM.MEM_SPEC_INTERP.interp_memory_prop. *)
                                                        (*   cbn. *)
                                                        (*   eapply orutt_interp_state; eauto. *)
                                                        (*   { unfold local_stack_refine_strict in *. *)
                                                        (*     destruct ls1, ls2; *)
                                                        (*     constructor; tauto. *)
                                                        (*   } *)

                                                        (*   intros A B e1 e2 s1 s2 H H0. *)
                                                        (*   eapply orutt_interp_local_stack_h; eauto. *)
                                                        (*   inv H0. *)
                                                        (*   destruct s1, s2; cbn in *; auto. *)

                                                        (*   intros A o s. *)
                                                        (*   exists o. *)
                                                        (*   cbn. *)
                                                        (*   setoid_rewrite bind_trigger. *)
                                                        (*   exists (fun x : A => SemNotations.Ret1 s x). *)
                                                        (*   reflexivity. *)
                                                        (* Qed. *)

                                                        Lemma model_E1E2_L3_orutt_strict_sound
                                                          (p : list
                                                                 (LLVMAst.toplevel_entity
                                                                    LLVMAst.typ
                                                                    (LLVMAst.block LLVMAst.typ * list (LLVMAst.block LLVMAst.typ)))) :
                                                          model_E1E2_L3_orutt_strict p p.
                                                        Proof.
                                                          apply model_E1E2_13_orutt_strict;
                                                            [ apply model_E1E2_L2_orutt_strict_sound
                                                            | apply local_stack_refine_strict_empty
                                                            ].
                                                        Qed.

                                                        (* If

    - ti2 is a refinement of ti1 tf2 refines ti2 tf1 refines tf2 at
    - finite level

    Not sure that this is true.

    If ti1 -i> ti2

    and ti2 -if> tf2

    And tf2 -f> tf1...

    Does it really follow that ti1 -if> tf1?

    In theory I can refine ti1 to ti2, and to tf1 through
    tf2... BUT... Does this mean I can refine ti1 directly to tf1?

    In theory ti2 has fewer behaviours than ti1, and so if I can
    refine it to tf2, then I can also refine ti1 to tf2.
                                                         *)
                                                        Lemma refine_E1E2_L6_strict_compose_inf_to_fin :
                                                          forall tx ty tz,
                                                            TLR_INF.R.refine_L6 tx ty ->
                                                            refine_E1E2_L6_strict ty tz ->
                                                            refine_E1E2_L6_strict tx tz.
                                                        Proof.
                                                          intros tx ty tz XY_INF YZ_FIN.

                                                          unfold refine_E1E2_L6_strict in *.
                                                          unfold TLR_INF.R.refine_L6 in *.
                                                          unfold TLR_FIN.R.refine_L6 in *.

                                                          intros rz TZ.
                                                          specialize (YZ_FIN rz TZ).
                                                          destruct YZ_FIN as (ry_fin & TY_FIN & YZ).

                                                          unfold L6_convert_PropT_strict in TY_FIN.
                                                          destruct TY_FIN as (ry_inf & TY_INF & ry_fin_inf).

                                                          specialize (XY_INF ry_inf TY_INF).
                                                          destruct XY_INF as (rx_inf & TX_INF & XY_INF).

                                                          set (rx_fin := L4_convert_tree_strict' res_L6_convert_strict_unsafe rx_inf).
                                                          exists rx_fin.
                                                          split.
                                                          - unfold L6_convert_PropT_strict, L4_convert_PropT_strict.
                                                            exists rx_inf; split; auto.
                                                            subst rx_fin.
                                                            reflexivity.
                                                          - rewrite <- YZ.
                                                            rewrite <- ry_fin_inf.
                                                            subst rx_fin.

                                                            (* There's probably a more general lemma hiding here *)
                                                            unfold L4_convert_tree_strict'.

                                                            Unset Universe Checking.
                                                            eapply refine_OOM_h_bind with (RR1:=TopLevelRefinementsBigIntptr.R.refine_res3).
                                                            { intros r1 r2 H.
                                                              unfold TLR_INF.R.refine_res3, TLR_INF.R.refine_res2, TLR_INF.R.refine_res1 in H.
                                                              destruct r1 as [r1a [r1sid [[r1b1 r1b2] [r1c dv1]]]].
                                                              destruct r2 as [r2a [r2sid [[r2b1 r2b2] [r2c dv2]]]].
                                                              cbn.

                                                              inversion H; subst.
                                                              inversion snd_rel; subst.
                                                              inversion snd_rel0; subst.
                                                              inversion snd_rel1; subst.
                                                              cbn in *; subst; reflexivity.
                                                            }
                                                            { apply refine_OOM_h_L6_convert_tree_strict; auto.
                                                            }
                                                        Qed.

                                                        Lemma refine_E1E2_L6_strict_compose_fin_to_inf :
                                                          forall tx ty tz,
                                                            refine_E1E2_L6_strict tx ty ->
                                                            TLR_FIN.R.refine_L6 ty tz ->
                                                            refine_E1E2_L6_strict tx tz.
                                                        Proof.
                                                          intros tx ty tz XY_INF_TO_FIN YZ_FIN.

                                                          unfold refine_E1E2_L6_strict in *.
                                                          unfold TLR_INF.R.refine_L6 in *.
                                                          unfold TLR_FIN.R.refine_L6 in *.

                                                          intros rz TZ.
                                                          specialize (YZ_FIN rz TZ).
                                                          destruct YZ_FIN as (ry_fin & TY_FIN & YZ).

                                                          specialize (XY_INF_TO_FIN ry_fin TY_FIN).
                                                          destruct XY_INF_TO_FIN as (rx_fin & TX_FIN & refine_inf_fin_x).

                                                          exists rx_fin.
                                                          split; auto.
                                                          rewrite refine_inf_fin_x; auto.
                                                        Qed.

                                                        Theorem refine_E1E2_L6_transitive :
                                                          forall ti1 ti2 tf1 tf2,
                                                            TLR_INF.R.refine_L6 ti1 ti2 ->
                                                            refine_E1E2_L6_strict ti2 tf1 ->
                                                            TLR_FIN.R.refine_L6 tf1 tf2 ->
                                                            refine_E1E2_L6_strict ti1 tf2.
                                                        Proof.
                                                          intros ti1 ti2 tf1 tf2 RINF RITOF RFIN.

                                                          eapply refine_E1E2_L6_strict_compose_fin_to_inf; eauto.
                                                          eapply refine_E1E2_L6_strict_compose_inf_to_fin; eauto.
                                                        Qed.

                                                        (** Safe conversion lemmas *)
                                                        (* TODO: These used the Fin to Inf LangRefine that no longer exists
     because we added safe conversion modules... See if I still need
     these *)
                                                        (* Lemma infinite_to_finite_dvalue_convert_safe : *)
                                                        (*   forall dv_i, *)
                                                        (*   exists dv_f, *)
                                                        (*     EC1.DVC.dvalue_convert_strict dv_i = NoOom dv_f /\ *)
                                                        (*       EC2.DVC.dvalue_convert_strict dv_f = NoOom dv_i. *)
                                                        (* Proof. *)
                                                        (*   intros dv_i. *)

                                                        (*   rewrite EC1.DVC.dvalue_convert_equation. *)
                                                        (*   destruct dv_i. *)
                                                        (*   - (* Addresses *) *)

                                                        (*   setoid_rewrite EC2.DVC.dvalue_convert_equation. *)

                                                        (*   (* TODO: Ugh, everything is opaque. Fix and prove. *) *)
                                                        (* Admitted. *)

                                                        (* Lemma L0_convert_safe : *)
                                                        (*   forall t, *)
                                                        (*     InfFinTC.L0_convert_tree' EC1.DVC.dvalue_convert *)
                                                        (*       (FinInfTC.L0_convert_tree' EC2.DVC.dvalue_convert t) ≈ t. *)
                                                        (* Proof. *)
                                                        (*   intros t. *)
                                                        (*   unfold InfFinTC.L0_convert_tree', InfFinTC.L0_convert_tree. *)
                                                        (*   unfold FinInfTC.L0_convert_tree', FinInfTC.L0_convert_tree. *)
                                                        (*   cbn. *)
                                                        (*   setoid_rewrite interp_bind. *)
                                                        (*   rewrite bind_bind. *)
                                                        (*   rewrite interp_interp. *)


                                                        (*   cbn. *)
                                                        (*   red. *)
                                                        (* Admitted. *)

                                                        (** Refinement lemmas *)
                                                        Lemma refine_E1E2_L0_strict_interp_intrinsics :
                                                          forall t1 t2,
                                                            refine_E1E2_L0_strict t1 t2 ->
                                                            refine_E1E2_L0_strict (InfLLVM.Intrinsics.interp_intrinsics t1) (FinLLVM.Intrinsics.interp_intrinsics t2).
                                                        Proof.
                                                          intros t1 t2 RL0.
                                                          red in RL0.
                                                          destruct RL0 as [t1' [OOM_T1 RL0]].
                                                          red in RL0.
                                                          red.
                                                          (* exists (FinInfTC.L0_convert_tree_strict' EC2.DVC.dvalue_convert (FinLLVM.Intrinsics.interp_intrinsics t2)). *)
                                                          (* split. *)
                                                          (* - assert ((FinInfTC.L0_convert_tree' EC2.DVC.dvalue_convert (FinLLVM.Intrinsics.interp_intrinsics t2)) ≈  (FinInfTC.L0_convert_tree' EC2.DVC.dvalue_convert (LLVM.Intrinsics.interp_intrinsics (InfFinTC.L0_convert_tree' EC1.DVC.dvalue_convert t1')))) as EQT2. *)
                                                          (*   { eapply @FinInfTC.L0_convert_tree'_eutt_proper with (RA:=eq). *)
                                                          (*     intros u1 u2 H; subst. *)
                                                          (*     reflexivity. *)

                                                          (*     rewrite RL0. *)
                                                          (*     reflexivity. *)
                                                          (*   } *)

                                                          (*   rewrite EQT2. *)

                                                          (*   eapply refine_OOM_h_transitive with (y:=(InfLLVM.Intrinsics.interp_intrinsics t1')); try typeclasses eauto. *)
                                                          (*   (* May hold... OOM_T1 *) *)
                                                          (*   admit. *)

                                                          (*   red. *)
                                                          (*   red. *)
                                                        (*   (* This might actually be provable by walking through t1'? *)

                                                         (*      The conversions may cause early OOM, but otherwise preserves *)
                                                         (*      the event structure. *)
                                                         (*    *) *)
                                                          (*   admit. *)
                                                          (* - red. *)
                                                        (*   (* This can't hold unless I know converting from E2 -> E1 -> E2 *)
                                                         (*      is "safe" and doesn't cause any OOM. *)

                                                         (*      This should be the case for the particular Inf / Fin case we *)
                                                         (*      care about, though. *)
                                                         (*    *) *)
                                                          (*   rewrite L0_convert_safe. *)
                                                          (*   reflexivity. *)
                                                        Admitted.

                                                        Lemma refine_E1E2_interp_global_strict :
                                                          forall t1 t2 g1 g2,
                                                            refine_E1E2_L0_strict t1 t2 ->
                                                            global_refine_strict g1 g2 ->
                                                            refine_E1E2_L1_strict (interp_global t1 g1) (interp_global t2 g2).
                                                        Proof.
                                                          intros t1 t2 g1 g2 RL0 GENVS.
                                                          red in RL0.
                                                          destruct RL0 as [t1' [OOM_T1 RL0]].
                                                          red.

                                                          (* Perhaps I need a lemma about L1_convert_tree and interp_global here? *)
                                                        Admitted.

                                                        Lemma refine_E1E2_interp_local_stack_strict :
                                                          forall t1 t2 ls1 ls2,
                                                            refine_E1E2_L1_strict t1 t2 ->
                                                            local_stack_refine_strict ls1 ls2 ->
                                                            refine_E1E2_L2_strict (interp_local_stack t1 ls1) (interp_local_stack t2 ls2).
                                                        Proof.
                                                        Admitted.

                                                        (* Most of these are aliases of the above, but some levels of the interpreter interpret more than one event *)
                                                        Lemma refine_E1E2_01_strict :
                                                          forall t1 t2 g1 g2,
                                                            refine_E1E2_L0_strict t1 t2 ->
                                                            global_refine_strict g1 g2 ->
                                                            refine_E1E2_L1_strict (interp_global (InfLLVM.Intrinsics.interp_intrinsics t1) g1) (interp_global (FinLLVM.Intrinsics.interp_intrinsics t2) g2).
                                                        Proof.
                                                          intros t1 t2 g1 g2 RL0 GENVS.
                                                          red in RL0.
                                                          apply refine_E1E2_interp_global_strict; auto.
                                                          apply refine_E1E2_L0_strict_interp_intrinsics; auto.
                                                        Qed.

                                                        Lemma refine_E1E2_12_strict :
                                                          forall t1 t2 l1 l2,
                                                            refine_E1E2_L1_strict t1 t2 ->
                                                            local_stack_refine_strict l1 l2 ->
                                                            refine_E1E2_L2_strict (interp_local_stack t1 l1) (interp_local_stack t2 l2).
                                                        Proof.
                                                          intros t1 t2 g1 g2 RL1 GENVS.
                                                          red in RL1.
                                                          apply refine_E1E2_interp_local_stack_strict; auto.
                                                        Qed.

                                                        Import InterpMemoryProp.
                                                        Lemma refine_E1E2_23_strict :
                                                          forall t1 t2 sid m1 m2,
                                                            refine_E1E2_L2_strict t1 t2 ->
                                                            MemState_refine m1 m2 ->
                                                            refine_E1E2_L3_strict (InfMemInterp.interp_memory_prop eq t1 sid m1) (FinMemInterp.interp_memory_prop eq t2 sid m2).
                                                        Proof.
                                                          intros t1 t2 sid m1 m2 RL2.

                                                        (*
    h1 and h2 are handlers

    (* h2 refines h1 *)
    (forall e,
    refine_E1E2_L3 (h1 e) (h2 e)) ->
    forall u : itree,
    refine_E1E2_L3 (interp_prop h1 u) (interp_prop h2 u)

    Need something a bit more general like rutt.

    (forall e1 e2,
    refine_events e1 e2 ->
    refine_E1E2_L3 (h1 e1) (h2 e2)) ->
    forall u1 u2 : itree,
    rutt refine_events refine_dvalue eq u1 u2 ->
    refine_E1E2_L3 (interp_prop h1 u1) (interp_prop h2 u2)


    (forall e1 e2,
    refine_events e1 e2 ->
    refine_E1E2_L4 (h1 e1) (h2 e2)) ->
    forall u1 u2 : itree,
    refine_E1E2_L3 u1 u2 ->
    refine_E1E2_L4 (interp_prop h1 u1) (interp_prop h2 u2)

                                                         *)

                                                          (* I'll probably need something about MemMonad_valid_state eventually... *)
                                                        Admitted.

                                                        Lemma refine_E1E2_34_strict :
                                                          forall t1 t2,
                                                            refine_E1E2_L3_strict t1 t2 ->
                                                            refine_E1E2_L4_strict (InfLLVM.Pick.model_undef eq t1) (FinLLVM.Pick.model_undef eq t2).
                                                        Proof.
                                                          intros t1 t2 RL3.
                                                          red.
                                                        Admitted.

                                                        Lemma refine_E1E2_45_strict :
                                                          forall t1 t2,
                                                            refine_E1E2_L4_strict t1 t2 ->
                                                            refine_E1E2_L5_strict (model_UB t1) (model_UB t2).
                                                        Proof.
                                                          intros t1 t2 RL4.
                                                          red.
                                                        Admitted.

                                                        Lemma refine_E1E2_56_strict :
                                                          forall t1 t2,
                                                            refine_E1E2_L5_strict t1 t2 ->
                                                            refine_E1E2_L6_strict (refine_OOM eq t1) (refine_OOM eq t2).
                                                        Proof.
                                                          intros t1 t2 RL4.
                                                          red.
                                                        Admitted.


                                                        From Vellvm Require Import Tactics.

                                                        From ITree Require Import
                                                          ITree
                                                          Basics.Monad
                                                          Events.StateFacts
                                                          Eq.Eqit.

                                                        Import TranslateFacts.
                                                        Import TopLevelBigIntptr.
                                                        Import TopLevel64BitIntptr.
                                                        Import InterpreterStackBigIntptr.
                                                        Import TopLevelRefinements64BitIntptr.

                                                        Ltac force_rewrite H :=
                                                          let HB := fresh "HB" in
                                                          pose proof @H as HB; eapply bisimulation_is_eq in HB; rewrite HB; clear HB.

                                                        Tactic Notation "force_rewrite" constr(H) "in" hyp(H') :=
                                                          let HB := fresh "HB" in
                                                          pose proof @H as HB; eapply bisimulation_is_eq in HB; rewrite HB in H'; clear HB.


                                                        (* TODO: this is going to be a big one *)
                                                        Theorem model_E1E2_L0_sound :
                                                          forall (p : LLVM_syntax),
                                                            model_E1E2_L0 p p.
                                                        Proof.
                                                          intros p.
                                                          unfold model_E1E2_L0.
                                                          red.
                                                          unfold refine_L0.
                                                          unfold L0_convert_tree_strict'.
                                                          unfold L0_convert_tree_strict.

                                                          (* exists (FinInfTC.L0_convert_tree_strict' EC2.DVC.dvalue_convert *)
                                                          (*      (denote_vellvm (DynamicTypes.DTYPE_I 32) "main" main_args *)
                                                          (*         (TypToDtyp.convert_types (CFG.mcfg_of_tle p)))). *)

                                                          (* split. *)
                                                          (* - (* src' may have additional OOM *) *)
                                                          (*   (* I think this pretty much has to be by induction over the syntax? *) *)
                                                          (*   admit. *)
                                                          (* - (* src' when converted agrees with target *) *)
                                                          (*   (* Target may just be OOM for all we know *) *)
                                                          (*   red. *)
                                                          (*   setoid_rewrite L0_convert_safe. *)
                                                          (*   reflexivity. *)
                                                        Admitted.

                                                        Theorem model_E1E2_L1_sound :
                                                          forall (p : LLVM_syntax),
                                                            model_E1E2_L1 p p.
                                                        Proof.
                                                          intros p.
                                                          red.

                                                          (* Maybe I need some lemmas akin to these:

    Lemma refine_34 : forall t1 t2,
        refine_L3 t1 t2 -> refine_L4 (model_undef refine_res3 t1) (model_undef refine_res3 t2).

    But for crossing the infinite / finite boundary...

                                                           *)
                                                          unfold model_oom_L1.
                                                          unfold model_gen_oom_L1.
                                                          unfold interp_mcfg1.

                                                          apply refine_E1E2_01_strict.
                                                          { (* Still need to deal with interp_intrinsics... *)
                                                            apply model_E1E2_L0_sound.
                                                          }

                                                          apply global_refine_strict_empty.
                                                        Qed.

                                                        Theorem model_E1E2_L2_sound :
                                                          forall (p : LLVM_syntax),
                                                            model_E1E2_L2 p p.
                                                        Proof.
                                                          intros p.
                                                          red.
                                                          apply refine_E1E2_12_strict; [| apply local_stack_refine_strict_empty].
                                                          apply model_E1E2_L1_sound.
                                                        Qed.

                                                        Theorem model_E1E2_L3_sound :
                                                          forall (p : LLVM_syntax),
                                                            model_E1E2_L3 p p.
                                                        Proof.
                                                          intros p.
                                                          red.
                                                          apply refine_E1E2_23_strict; [| apply MemState_refine_initial].
                                                          apply model_E1E2_L2_sound.
                                                        Qed.

                                                        Theorem model_E1E2_L4_sound :
                                                          forall (p : LLVM_syntax),
                                                            model_E1E2_L4 p p.
                                                        Proof.
                                                          intros p.
                                                          red.
                                                          apply refine_E1E2_34_strict.
                                                          apply model_E1E2_L3_sound.
                                                        Qed.

                                                        Theorem model_E1E2_L5_sound :
                                                          forall (p : LLVM_syntax),
                                                            model_E1E2_L5 p p.
                                                        Proof.
                                                          intros p.
                                                          red.
                                                          apply refine_E1E2_45_strict.
                                                          apply model_E1E2_L4_sound.
                                                        Qed.

                                                        Theorem model_E1E2_L6_sound :
                                                          forall (p : LLVM_syntax),
                                                            model_E1E2_L6 p p.
                                                        Proof.
                                                          intros p.
                                                          red.
                                                          apply refine_E1E2_56_strict.
                                                          apply model_E1E2_L5_sound.
                                                        Qed.

                                                        End InfiniteToFinite.
