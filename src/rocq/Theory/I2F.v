From Equations Require Import Equations.

From Stdlib Require Import Lia.

From ExtLib Require Import Structures.Monads.

From ITree Require Import ITree Eq HeterogeneousRelations.

From Vellvm Require Import
  Utils
  Syntax
  Integers
  DynamicValues
  EOU
  LLVMEvents
  Interfaces.IPtr
  Interfaces.Params
  Implementations.Address
  Implementations.Provenance
  Implementations.IPtrInfinite
  Implementations.IPtrFinite
  Implementations.Memory
  Implementations.ParamsV
  Denotation.

From Vellvm Require Import
  Theory.rutt_cutoff.

From Paco Require Import paco.

(* I want versions that compute to reduce in proofs rather than nest constructors/inversions *)
Definition sum_prerel {E1 E2 D1 D2 : Type -> Type} (PR1 : prerel E1 D1 ) (PR2 : prerel E2 D2) 
  : prerel (E1 +' E2) (D1 +' D2) :=
  fun A B e1 e2 =>
    match e1,e2 with
    | inl1 e1, inl1 e2 => PR1 _ _ e1 e2
    | inr1 e1, inr1 e2 => PR2 _ _ e1 e2
    | _,_ => False
    end
.

Definition sum_postrel {E1 E2 D1 D2 : Type -> Type} (PR1 : postrel E1 D1 ) (PR2 : postrel E2 D2) 
  : postrel (E1 +' E2) (D1 +' D2) :=
  fun A B e1 a e2 b => 
    match e1,e2 with
    | inl1 e1, inl1 e2 => PR1 _ _ e1 a e2 b
    | inr1 e1, inr1 e2 => PR2 _ _ e1 a e2 b
    | _,_ => False
    end
.

Section Refinement.

  Definition PInf : Params := @ParamsV IPZ IPZTheory.
  Definition PFin : Params := @ParamsV IP64Bit IP64BitTheory.

  (** * Value relations *)

  Definition I2F_Iptr : @iptr IPZ -> @iptr IP64Bit -> Prop :=
    fun z i => z = unsigned i.

  Definition I2F_Addr : @addr ProvenanceV (@AddressV IPZ) -> @addr ProvenanceV (@AddressV IP64Bit) -> Prop :=
    fun '(z,p) '(i,p') => I2F_Iptr z i /\ p = p'.

  Inductive I2F_dvalue : @dvalue PInf -> @dvalue PFin -> Prop :=
  | I2F_dvalue_Addr a a' :
    I2F_Addr a a' ->
    I2F_dvalue (@DVALUE_Addr PInf a) (@DVALUE_Addr PFin a')
  | I2F_dvalue_Int sz i :
    I2F_dvalue (DVALUE_I sz i) (DVALUE_I sz i)
  | I2F_dvalue_Ptr p p' :
    I2F_Iptr p p' ->
    I2F_dvalue (@DVALUE_Iptr PInf p) (@DVALUE_Iptr PFin p')
  | I2F_dvalue_Double d :
    I2F_dvalue (DVALUE_Double d) (DVALUE_Double d)
  | I2F_dvalue_Float f :
    I2F_dvalue (DVALUE_Float f) (DVALUE_Float f)
  | I2F_dvalue_Poison τ :
    I2F_dvalue (DVALUE_Poison τ) (DVALUE_Poison τ)
  | I2F_dvalue_None :
    I2F_dvalue DVALUE_None DVALUE_None
  | I2F_dvalue_Struct s1 s2 :
    Forall2 I2F_dvalue s1 s2 ->
    I2F_dvalue (DVALUE_Struct s1) (DVALUE_Struct s2)
  | I2F_dvalue_Packed_struct s1 s2 :
    Forall2 I2F_dvalue s1 s2 ->
    I2F_dvalue (DVALUE_Packed_struct s1) (DVALUE_Packed_struct s2)
  | I2F_dvalue_Array τ s1 s2 :
    Forall2 I2F_dvalue s1 s2 ->
    I2F_dvalue (DVALUE_Array τ s1) (DVALUE_Array τ s2)
  | I2F_dvalue_Vector τ s1 s2 :
    Forall2 I2F_dvalue s1 s2 ->
    I2F_dvalue (DVALUE_Vector τ s1) (DVALUE_Vector τ s2)
  .
  Hint Constructors I2F_dvalue : core.

  (* Exceptions are dvalues, and calls/intrinsics answer in [exc + dvalue] *)
  Notation I2F_exc_dvalue := (sum_rel I2F_dvalue I2F_dvalue).

  (** Relating pure computations in the [EOU] monad, mirroring the cut
      structure of [ruttc] (see [I2F_refine_lift]): lockstep on returns
      and errors, while UB on the infinite (left) side and OOM on the
      finite (right) side short-circuit. *)
  Variant I2F_EOU {A1 A2} (RR : A1 -> A2 -> Prop) : EOU A1 -> EOU A2 -> Prop :=
    | I2F_EOU_ret a1 a2 : RR a1 a2 -> I2F_EOU RR (raise_ret a1) (raise_ret a2)
    | I2F_EOU_error s1 s2 : I2F_EOU RR (raise_error s1) (raise_error s2)
    | I2F_EOU_ub s m : I2F_EOU RR (raise_ub s) m
    | I2F_EOU_oom m s : I2F_EOU RR m (raise_oom s)
  .
  #[local] Hint Constructors I2F_EOU : core.

  (** * Event relations, one per event family

      Two events are related when they are the same constructor, carrying
      pointwise [I2F]-related payloads. Recall the components that do not
      mention values ([raw_id], [dtyp], intrinsic names, [int8] streams,
      the [unit] messages of the abortive events) are shared between the
      two instantiations, hence required equal. *)

  Equations I2FE_Call : prerel (@CallE PInf) (@CallE PFin) :=
    I2FE_Call (@Call PInf τ1 f1 args1) (@Call PFin τ2 f2 args2) :=
      τ1 = τ2 /\ I2F_dvalue f1 f2 /\ Forall2 I2F_dvalue args1 args2.

  Equations I2FE_ExternalCall : prerel (@ExternalCallE PInf) (@ExternalCallE PFin) :=
    I2FE_ExternalCall (@ExternalCall PInf τ1 f1 args1) (@ExternalCall PFin τ2 f2 args2) :=
      τ1 = τ2 /\ I2F_dvalue f1 f2 /\ Forall2 I2F_dvalue args1 args2;
    I2FE_ExternalCall (@IO_stdout PInf str1) (@IO_stdout PFin str2) := str1 = str2;
    I2FE_ExternalCall (@IO_stderr PInf str1) (@IO_stderr PFin str2) := str1 = str2;
    I2FE_ExternalCall _ _ := False.

  Equations I2FE_Intrinsic : prerel (@IntrinsicE PInf) (@IntrinsicE PFin) :=
    I2FE_Intrinsic (@Intrinsic PInf τ1 f1 args1 va1) (@Intrinsic PFin τ2 f2 args2 va2) :=
      τ1 = τ2 /\ f1 = f2 /\ Forall2 I2F_dvalue args1 args2 /\ option_rel I2F_Addr va1 va2.

  Equations I2FE_Global : prerel (@GlobalE PInf) (@GlobalE PFin) :=
    I2FE_Global (@GlobalWrite PInf x1 dv1) (@GlobalWrite PFin x2 dv2) :=
      x1 = x2 /\ I2F_dvalue dv1 dv2;
    I2FE_Global (@GlobalRead PInf x1) (@GlobalRead PFin x2) := x1 = x2;
    I2FE_Global _ _ := False.

  Equations I2FE_Local : prerel (@LocalE PInf) (@LocalE PFin) :=
    I2FE_Local (@LocalWrite PInf x1 dv1) (@LocalWrite PFin x2 dv2) :=
      x1 = x2 /\ I2F_dvalue dv1 dv2;
    I2FE_Local (@LocalRead PInf x1) (@LocalRead PFin x2) := x1 = x2;
    I2FE_Local _ _ := False.

  Equations I2FE_Stack : prerel (@StackE PInf) (@StackE PFin) :=
    I2FE_Stack (@StackPush PInf args1) (@StackPush PFin args2) :=
      Forall2 (prod_rel Logic.eq I2F_dvalue) args1 args2;
    I2FE_Stack (@StackPop PInf) (@StackPop PFin) := True;
    I2FE_Stack (@StackRaise PInf exc1) (@StackRaise PFin exc2) := I2F_dvalue exc1 exc2;
    I2FE_Stack (@StackGetExc PInf) (@StackGetExc PFin) := True;
    I2FE_Stack _ _ := False.

  Equations I2FE_Memory : prerel (@MemoryE PInf) (@MemoryE PFin) :=
    I2FE_Memory (@MemPush PInf) (@MemPush PFin) := True;
    I2FE_Memory (@MemPop PInf) (@MemPop PFin) := True;
    I2FE_Memory (@Alloca PInf τ1 n1 align1) (@Alloca PFin τ2 n2 align2) :=
      τ1 = τ2 /\ n1 = n2 /\ align1 = align2;
    I2FE_Memory (@Load PInf τ1 a1) (@Load PFin τ2 a2) :=
      τ1 = τ2 /\ I2F_dvalue a1 a2;
    I2FE_Memory (@Store PInf τ1 a1 v1) (@Store PFin τ2 a2 v2) :=
      τ1 = τ2 /\ I2F_dvalue a1 a2 /\ I2F_dvalue v1 v2;
    I2FE_Memory _ _ := False.

  Equations I2FE_Draw : prerel (@DrawE PInf) (@DrawE PFin) :=
    I2FE_Draw (@Draw PInf τ1) (@Draw PFin τ2) := τ1 = τ2.

  Equations I2FE_Exc : prerel (@LLVMExcE PInf) (@LLVMExcE PFin) :=
    I2FE_Exc (@LLVMExc PInf exc1) (@LLVMExc PFin exc2) := I2F_dvalue exc1 exc2.

  (* [OOME], [UBE], [DebugE], [FailureE] do not mention values: they are
     shared by both instantiations. Note that pairs of related [OOME]
     (resp. [UBE]) events can alternatively be discharged by the cut
     mechanism of [ruttc] --- see [I2F_refine] below. *)

  Equations I2FE_OOM : prerel OOME OOME :=
    I2FE_OOM (ThrowOOM u1) (ThrowOOM u2) := True.

  Equations I2FE_UB : prerel UBE UBE :=
    I2FE_UB (ThrowUB u1) (ThrowUB u2) := True.

  Equations I2FE_Debug : prerel DebugE DebugE :=
    I2FE_Debug (Debug u1) (Debug u2) := True.

  Equations I2FE_Failure : prerel FailureE FailureE :=
    I2FE_Failure (Throw u1) (Throw u2) := True.

  (** * Answer relations, one per event family

      [ruttc] additionally takes a relation on the answers returned to two
      related events: when relating [Vis e1 k1] with [Vis e2 k2], the
      continuations only have to be related on pairs of answers related by
      it. It is our relational assumption on the environment, to be
      discharged when interpreting each event family: the answers are
      related by the [I2F] value relation matching the answer type of the
      event --- [I2F_dvalue] on [dvalue] answers, its [sum_rel]
      (resp. [option_rel]) lifting on [exc + dvalue] (resp. [option exc])
      answers, trivial on [unit], and vacuous on [void] (abortive events
      never answer). *)

  Equations I2FA_Call : postrel (@CallE PInf) (@CallE PFin) :=
    I2FA_Call (@Call PInf τ1 f1 args1) r1 (@Call PFin τ2 f2 args2) r2 := I2F_exc_dvalue r1 r2.

  Equations I2FA_ExternalCall : postrel (@ExternalCallE PInf) (@ExternalCallE PFin) :=
    I2FA_ExternalCall (@ExternalCall PInf τ1 f1 args1) dv1 (@ExternalCall PFin τ2 f2 args2) dv2 := I2F_dvalue dv1 dv2;
    I2FA_ExternalCall (@IO_stdout PInf str1) a (@IO_stdout PFin str2) b := True;
    I2FA_ExternalCall (@IO_stderr PInf str1) a (@IO_stderr PFin str2) b := True;
    I2FA_ExternalCall _ _ _ _ := False.

  Equations I2FA_Intrinsic : postrel (@IntrinsicE PInf) (@IntrinsicE PFin) :=
    I2FA_Intrinsic (@Intrinsic PInf τ1 f1 args1 va1) r1 (@Intrinsic PFin τ2 f2 args2 va2) r2 := I2F_exc_dvalue r1 r2.

  Equations I2FA_Global : postrel (@GlobalE PInf) (@GlobalE PFin) :=
    I2FA_Global (@GlobalWrite PInf x1 dv1) a (@GlobalWrite PFin x2 dv2) b := True;
    I2FA_Global (@GlobalRead PInf x1) dv1 (@GlobalRead PFin x2) dv2 := I2F_dvalue dv1 dv2 ;
    I2FA_Global _ _ _ _ := False.
  
  Equations I2FA_Local : postrel (@LocalE PInf) (@LocalE PFin) :=
    I2FA_Local (@LocalWrite PInf x1 dv1) a (@LocalWrite PFin x2 dv2) b := True;
    I2FA_Local (@LocalRead PInf x1) dv1 (@LocalRead PFin x2) dv2 := I2F_dvalue dv1 dv2;
    I2FA_Local _ _ _ _ := False.

  Equations I2FA_Stack : postrel (@StackE PInf) (@StackE PFin) :=
    I2FA_Stack (@StackPush PInf args1) a (@StackPush PFin args2) b := True;
    I2FA_Stack (@StackPop PInf) a (@StackPop PFin) b := True;
    I2FA_Stack (@StackRaise PInf exc1) a (@StackRaise PFin exc2) b := True;
    I2FA_Stack (@StackGetExc PInf) oe1 (@StackGetExc PFin) oe2 := option_rel I2F_dvalue oe1 oe2;
    I2FA_Stack _ _ _ _ := False.

  (* [Alloca] answers with the fresh address wrapped as a [dvalue]:
     the two memories allocate at [I2F_Addr]-related addresses. *)
  Equations I2FA_Memory : postrel (@MemoryE PInf) (@MemoryE PFin) :=
    I2FA_Memory (@MemPush PInf) a (@MemPush PFin) b := True;
    I2FA_Memory (@MemPop PInf) a (@MemPop PFin) b := True;
    I2FA_Memory (@Alloca PInf τ1 n1 align1) dv1 (@Alloca PFin τ2 n2 align2) dv2 := I2F_dvalue dv1 dv2;
    I2FA_Memory (@Load PInf τ1 a1) dv1 (@Load PFin τ2 a2) dv2 := I2F_dvalue dv1 dv2;
    I2FA_Memory (@Store PInf τ1 a1 v1) a (@Store PFin τ2 a2 v2) b := True;
    I2FA_Memory _ _ _ _ := False.

  Equations I2FA_Draw : postrel (@DrawE PInf) (@DrawE PFin) :=
    I2FA_Draw (@Draw PInf τ1) dv1 (@Draw PFin τ2) dv2 := I2F_dvalue dv1 dv2.

  (* The abortive events answer in [void]: their answer relations are
     vacuous ([False] bodies), and so are the associated continuation
     proof obligations. *)

  Equations I2FA_Exc : postrel (@LLVMExcE PInf) (@LLVMExcE PFin) :=
    I2FA_Exc (@LLVMExc PInf exc1) a (@LLVMExc PFin exc2) b := False.

  Equations I2FA_OOM : postrel OOME OOME :=
    I2FA_OOM (ThrowOOM u1) a (ThrowOOM u2) b := False.

  Equations I2FA_UB : postrel UBE UBE :=
    I2FA_UB (ThrowUB u1) a (ThrowUB u2) b := False.

  Equations I2FA_Debug : postrel DebugE DebugE :=
    I2FA_Debug (Debug u1) a (Debug u2) b := True.

  Equations I2FA_Failure : postrel FailureE FailureE :=
    I2FA_Failure (Throw u1) a (Throw u2) b := False.

  (** * Combined relations on [MCFGEtop] and [CFGEtop]

      The per-family relations are glued along the structure of the event
      signatures with [sum_prerel]/[sum_postrel]. This is the format
      expected by the [mrec] reasoning principle
      ([RuttFacts.interp_mrec_rutt] and its [ruttc] analogue to come):
      since [CFGEtop ≡ CallE +' MCFGEtop] and [denote_mcfg] is an [mrec]
      over [CallE], the [CFG]-level relations are literally
      [sum_prerel I2FE_Call I2FE_MCFG] / [sum_postrel I2FA_Call I2FA_MCFG]. *)

  Definition I2FE_MCFG : prerel (@MCFGEtop PInf) (@MCFGEtop PFin) :=
    sum_prerel I2FE_ExternalCall
      (sum_prerel I2FE_Intrinsic
         (sum_prerel I2FE_Global
            (sum_prerel (sum_prerel I2FE_Local I2FE_Stack)
               (sum_prerel I2FE_Memory
                  (sum_prerel I2FE_Draw
                     (sum_prerel I2FE_OOM
                        (sum_prerel I2FE_Exc
                           (sum_prerel I2FE_UB
                              (sum_prerel I2FE_Debug I2FE_Failure))))))))).

  Definition I2FA_MCFG : postrel (@MCFGEtop PInf) (@MCFGEtop PFin) :=
    sum_postrel I2FA_ExternalCall
      (sum_postrel I2FA_Intrinsic
         (sum_postrel I2FA_Global
            (sum_postrel (sum_postrel I2FA_Local I2FA_Stack)
               (sum_postrel I2FA_Memory
                  (sum_postrel I2FA_Draw
                     (sum_postrel I2FA_OOM
                        (sum_postrel I2FA_Exc
                           (sum_postrel I2FA_UB
                              (sum_postrel I2FA_Debug I2FA_Failure))))))))).

  Definition I2FE_CFG : prerel (@CFGEtop PInf) (@CFGEtop PFin) :=
    sum_prerel I2FE_Call I2FE_MCFG.

  Definition I2FA_CFG : postrel (@CFGEtop PInf) (@CFGEtop PFin) :=
    sum_postrel I2FA_Call I2FA_MCFG.

  (** * The refinement relation *)

  Variant cutUB {E} `{UBE -< E} : forall [A], E A -> Prop :=
    | CutUB v : cutUB (subevent _ (ThrowUB v)).

  Variant cutOOM {E} `{OOME -< E} : forall [A], E A -> Prop :=
    | CutOOM v : cutOOM (subevent _ (ThrowOOM v)).

  (* The infinite computation (left) and the finite one (right) proceed in
     lockstep over [I2FE]-related events answered by [I2FA]-related values,
     except that the equivalence is short-circuited if the finite side runs
     out of memory (cut on OOM on the right); UB should arise simultaneously
     on both sides, so we may cut it off on the left. *)

  Definition I2F_refine_MCFG {R1 R2} (RR : R1 -> R2 -> Prop)
    : @MCFGtop PInf R1 -> @MCFGtop PFin R2 -> Prop :=
    ruttc cutUB cutOOM I2FE_MCFG I2FA_MCFG RR.

  Definition I2F_refine_CFG {R1 R2} (RR : R1 -> R2 -> Prop)
    : @CFGtop PInf R1 -> @CFGtop PFin R2 -> Prop :=
    ruttc cutUB cutOOM I2FE_CFG I2FA_CFG RR.

  Definition I2F_refine : @MCFGtop PInf (@dvalue PInf) -> @MCFGtop PFin (@dvalue PFin) -> Prop :=
    I2F_refine_MCFG I2F_dvalue.

  (** Lifting [I2F_EOU]-related pure computations into the refinement.
      This is the workhorse for all the arithmetic cases of [denote_exp]:
      they end in [lift (f ...)] for pure [f]s, so each of them reduces to
      an [I2F_EOU] fact about [f], proved by first-order case analysis. *)
  Lemma I2F_refine_lift {R1 R2} (RR : R1 -> R2 -> Prop) (m1 : EOU R1) (m2 : EOU R2) :
    I2F_EOU RR m1 m2 ->
    I2F_refine_MCFG RR (EOU_to_itree m1) (EOU_to_itree m2).
  Proof.
    intros []; cbn.
    - pfold; constructor; auto.
    - apply ruttc_trigger_cast; easy.
    - pfold; red; cbn.
      apply EqCutL; constructor.
    - pfold; red; cbn.
      apply EqCutR; constructor.
  Qed.

  (* [denote_exp] only ever applies [EOU_to_itree] to pure computations we
     relate through [I2F_refine_lift]; prevent [cbn] from unfolding it into
     a stuck match that would obstruct applying the lemma. *)
  #[local] Arguments EOU_to_itree : simpl never.

(* Lemma I2F_refine_MCFG_trigger {A B} (e : @MCFGEtop PInf A) (f : @MCFGEtop PFin B) RR : *)
(*   I2FE_MCFG e f -> *)
(*   I2F_refine_MCFG RR (ITree.trigger e) (ITree.trigger f). *)
(* Proof. *)
(*   intros; apply ruttc_trigger; auto. *)
   
  (* Hint Constructors I2FA_Local. *) (* I2FA_Local is now an Equations definition, no constructors *)

  Tactic Notation "simp_id" := cbn; cbv[resum ReSum_id id_ Id_IFun].
  Tactic Notation "simp_id" "in" ident(H) := cbn in H; cbv[resum ReSum_id id_ Id_IFun] in H.

  Tactic Notation "simp!" :=
    simp I2FE_Call I2FE_ExternalCall I2FE_Intrinsic I2FE_Global I2FE_Local I2FE_Stack I2FE_Memory I2FE_Draw
         in *.

  Ltac rew H :=
    autorewrite with
      I2FE_Call I2FE_ExternalCall I2FE_Intrinsic
      I2FE_Global I2FE_Local
      I2FE_Stack I2FE_Memory I2FE_Draw
      I2FE_Failure I2FE_OOM I2FE_UB
      (* I2FA_Call I2FA_AxternalCall I2FA_Intrinsic I2FA_Global I2FA_Local I2FA_Stack I2FA_Memory I2FA_Draw *)
      in H.
  
  (** The pure content of the [EXP_Integer] case, and the one place where
      the 14-way case analysis on [dtyp] happens. *)
  Lemma I2F_denote_int_syntax_as_int : forall τ x,
      I2F_EOU I2F_dvalue
        (@denote_int_syntax_as_int PInf τ x)
        (@denote_int_syntax_as_int PFin τ x).
  Proof.
    intros; destruct τ; cbn; try (now repeat constructor).
    (* [DTYPE_Iptr]: the finite side either OOMs ([I2F_EOU_oom]) or
       returns [repr x] with [x] in range, so that [unsigned (repr x) = x]. *)
    unfold from_Z_bits.
    destruct ((denote_int_syntax x <=? @Integers.max_unsigned 64)%Z
                && (denote_int_syntax x >=? 0)%Z) eqn:EQ; cbn.
    - apply andb_prop in EQ as [LE GE].
      apply Z.leb_le in LE; apply Z.geb_le in GE.
      do 2 constructor.
      red; rewrite Integers.unsigned_repr; [reflexivity | lia].
    - constructor.
  Qed.

  (** The pure content of the [EXP_Float] case. The float parsing is
      parameter-independent: both sides run the very same computation. *)
  Lemma I2F_denote_float_syntax_as_float : forall τ x,
      I2F_EOU I2F_dvalue
        (@denote_float_syntax_as_float PInf τ x)
        (@denote_float_syntax_as_float PFin τ x).
  Proof.
    intros; destruct τ; cbn; try (now repeat constructor).
    repeat (break_match_goal; cbn); now repeat constructor.
  Qed.

  (** Compatibility of [I2F_EOU] with the monadic structure of [EOU]. *)
  Lemma I2F_EOU_bind {A1 A2 B1 B2} (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop)
        (m1 : EOU A1) (m2 : EOU A2) (k1 : A1 -> EOU B1) (k2 : A2 -> EOU B2) :
    I2F_EOU RA m1 m2 ->
    (forall a1 a2, RA a1 a2 -> I2F_EOU RB (k1 a1) (k2 a2)) ->
    I2F_EOU RB (bind m1 k1) (bind m2 k2).
  Proof.
    intros [] KEQ; cbn; eauto.
  Qed.

  Lemma I2F_EOU_map_monad {A B1 B2} (RB : B1 -> B2 -> Prop)
        (f1 : A -> EOU B1) (f2 : A -> EOU B2) (l : list A) :
    (forall a, In a l -> I2F_EOU RB (f1 a) (f2 a)) ->
    I2F_EOU (Forall2 RB) (map_monad f1 l) (map_monad f2 l).
  Proof.
    induction l as [| a l IH]; intros HIN; cbn.
    - now constructor.
    - eapply I2F_EOU_bind; [apply HIN; now left|].
      intros b1 b2 HB.
      eapply I2F_EOU_bind; [apply IH; intros; apply HIN; now right|].
      intros bs1 bs2 HBS.
      do 2 constructor; auto.
  Qed.

  Lemma Forall2_repeat {A B} (R : A -> B -> Prop) a b n :
    R a b -> Forall2 R (repeat a n) (repeat b n).
  Proof.
    induction n; cbn; intros; constructor; auto.
  Qed.

  (* The zero intptr and the null address of the two models are related. *)
  Lemma I2F_Iptr_zero : I2F_Iptr zero_iptr zero_iptr.
  Proof.
    red; cbn; rewrite ?Integers.unsigned_zero; easy.
  Qed.

  Lemma I2F_Addr_null : I2F_Addr null null.
  Proof.
    cbn; split; [apply I2F_Iptr_zero | reflexivity].
  Qed.

  (* [Extern]/[apply] rather than [Resolve]/[simple apply]: the goals show
     the instance-reduced forms of [zero_iptr]/[null], which only match the
     lemmas up to conversion. *)
  #[local] Hint Extern 1 (I2F_Iptr _ _) => apply I2F_Iptr_zero : core.
  #[local] Hint Extern 1 (I2F_Addr _ _) => apply I2F_Addr_null : core.
  #[local] Hint Resolve Forall2_repeat : core.

  (** The pure content of the [EXP_Zero_initializer] case, by induction on
      [dtyp]. The only value-dependent leaves are [DTYPE_Iptr] (the zero
      intptr on both sides) and [DTYPE_Pointer] ([null] on both sides),
      including under vectors; the aggregate cases go through the
      compatibility of [I2F_EOU] with [bind] and [map_monad]. *)
  Lemma I2F_default_dvalue_of_dtyp : forall τ,
      I2F_EOU I2F_dvalue
        (@default_dvalue_of_dtyp PInf τ)
        (@default_dvalue_of_dtyp PFin τ).
  Proof.
    induction τ; cbn; auto 6.
    - (* DTYPE_I *)
      unfold default_dvalue_of_dtyp_i; auto.
    - (* DTYPE_FP *)
      repeat (break_match_goal; cbn); auto.
    - (* DTYPE_Array *)
      eapply I2F_EOU_bind; [eassumption|].
      intros; do 2 constructor; auto.
    - (* DTYPE_Struct *)
      eapply I2F_EOU_bind; [apply I2F_EOU_map_monad; auto|].
      intros; do 2 constructor; auto.
    - (* DTYPE_Packed_struct *)
      eapply I2F_EOU_bind; [apply I2F_EOU_map_monad; auto|].
      intros; do 2 constructor; auto.
    - (* DTYPE_Vector *)
      repeat (break_match_goal; cbn);
        unfold default_dvalue_of_dtyp_i; auto 6.
  Qed.

  Lemma I2F_denote_expr :
    forall (e : exp dtyp) τ, I2F_refine (@denote_exp PInf τ e) (@denote_exp PFin τ e).
  Proof.
    apply (@exp_ind_full dtyp (fun e => forall τ, I2F_refine (@denote_exp PInf τ e) (@denote_exp PFin τ e)) (fun _ => True)); auto.
    - intros; cbn.
      destruct id; cbn.
      + apply ruttc_trigger; easy.
      + apply ruttc_trigger; easy.
    - intros x [d|]; cbn.
      2: apply ruttc_trigger_cast; easy.
      apply I2F_refine_lift, I2F_denote_int_syntax_as_int.
    - intros x [d|]; cbn.
      2: apply ruttc_trigger_cast; easy.
      apply I2F_refine_lift, I2F_denote_float_syntax_as_float.
    - intros [] ?; cbn; apply ruttc_ret; eauto.
    - intros; cbn; apply ruttc_ret.
      constructor; cbn; intuition; reflexivity.
    - (* initializer *)
      intros [d|]; cbn.
      2: apply ruttc_trigger_cast; easy.
      apply I2F_refine_lift, I2F_default_dvalue_of_dtyp.
Admitted.      


End Refinement.
