(* begin hide *)
From Coq Require Import
     String Morphisms.

Require Import List.
Import ListNotations.

From ITree Require Import
     ITree
     Basics.Monad
     Eq.Eqit
     TranslateFacts.

From Vellvm Require Import
     Utilities
     Utils.MapMonadExtra
     Semantics
     Theory.InterpreterCFG
     TopLevelRefinements.

From ExtLib.Data.Monads Require Import EitherMonad IdentityMonad.
Import ExtLib.Structures.Functor.

Open Scope list_scope.
Open Scope itree_scope.

Import ITreeNotations.

Module InstrLemmas (IS : InterpreterStackBig) (TOP : LLVMTopLevel IS) (REFS: TopLevelRefinements IS TOP).
  Module CFGT := CFGTheory IS TOP.


  Export CFGT.
  Export TOP.
  Export IS.
  Export IS.LLVM.
  Import SemNotations.
  Import REFS.
  (* end hide *)

  (** * Lemmas related to the semantics of instructions (and terminators)
  This file contains essentially proof rules specifying the behavior of instructions,
   allowing for symbolic execution in refinement proofs.
   *)

  (** Helper lemmas that should probably be moved *)
  (* TODO: Move this *)
  Lemma interp_cfg2_concretize_or_pick_concrete :
    forall (uv : uvalue) (dv : dvalue) g l,
      is_concrete uv = true ->
      uvalue_to_dvalue uv = inr dv ->
      ℑ2 (concretize_or_pick uv) g l ≈ Ret2 g l dv.
  Proof.
    intros * CONC CONV.
    unfold concretize_or_pick.
    rewrite CONC.
    cbn.
    unfold lift_err.
    rewrite CONV.
    rewrite interp_cfg2_ret.
    reflexivity.
  Qed.

  (* TODO: Move this *)
  Lemma interp_cfg3_concretize_or_pick_concrete_exists :
    forall (uv : uvalue) g l,
      is_concrete uv = true ->
      exists dv, uvalue_to_dvalue uv = inr dv /\ ℑ2 (concretize_or_pick uv) g l ≈ Ret2 g l dv.
  Proof.
    intros uv g ρ CONC.
    pose proof is_concrete_uvalue_to_dvalue uv CONC as (dv & CONV).
    exists dv.
    split; auto.
    apply interp_cfg2_concretize_or_pick_concrete; auto.
  Qed.

  (* TODO; Move this *)
  Lemma interp_cfg2_concretize_or_pick_not_concrete :
    forall (uv : uvalue) (dv : dvalue) g l,
      is_concrete uv = false ->
      ℑ2 (concretize_or_pick uv) g l ≈ 'dv <- trigger (pick_uvalue uv) ;; Ret2 g l (proj1_sig dv).
  Proof.
    intros uv dv g ρ NCONC.
    unfold concretize_or_pick.
    rewrite NCONC.
    setoid_rewrite interp_cfg2_pick_proj1_sig.
    reflexivity.
  Qed.

  (** Lemmas about denote_instr *)

  Module InstrTactics.

    Hint Rewrite @bind_ret_l : rwexp.
    Hint Rewrite @translate_ret : rwexp.
    Hint Rewrite @interp_cfg2_ret : rwexp.
    Hint Rewrite @translate_bind : rwexp.
    Hint Rewrite @interp_cfg2_bind : rwexp.
    Hint Rewrite @translate_trigger : rwexp.

    Ltac go := autorewrite with rwexp.

    Ltac step :=
      match goal with
      | |- context [trigger (GlobalRead _)] =>
          match goal with
          | h: Maps.lookup _ _ = Some _ |- _ =>
              rewrite interp_cfg2_GR; [rewrite ?bind_ret_l | eauto]
          | h: Maps.lookup _ _ = None |- _ =>
              rewrite interp_cfg2_GR_fail; [rewrite ?bind_ret_l | eauto]
          end
      | |- context [trigger (LocalRead _)] =>
          match goal with
          | h: Maps.lookup _ _ = Some _ |- _ =>
              rewrite interp_cfg2_LR; [rewrite ?bind_ret_l | eauto]
          | h: Maps.lookup _ _ = None |- _ =>
              rewrite interp_cfg2_LR_fail; [rewrite ?bind_ret_l | eauto]
          end
      (* | |- context [trigger (Load _ _)] => rewrite interp_cfg3_Load; [rewrite ?bind_ret_l | eauto] *)
      (* | |- context [trigger (Store _ _)] => rewrite interp_cfg3_store; [rewrite ?bind_ret_l | eauto] *)
      | |- context [trigger (LocalWrite _ _)] => rewrite interp_cfg2_LW
      | |- context [trigger (GlobalWrite _ _)] => rewrite interp_cfg2_GW
      end.

  Ltac ev_subevent_condense_step ev :=
    match ev with
      | subevent _ _ => rewrite subevent_subevent
      | inr1 _ => rewrite <- subevent_right
      | inl1 _ => rewrite <- subevent_left
      | @resum _ _ _ _ _ _ _ => unfold resum, ReSum_id, id_, Id_IFun
    end.
  Ltac ev_subevent_condense ev := repeat ev_subevent_condense_step ev.
  Ltac process :=
    repeat match goal with
      | |- _ (_ <- ?first_body;; _) _ => match first_body with
        |  _ (trigger ?ev) _ _ => ev_subevent_condense_step ev
        |  _ (Vis ?ev _) _ _ => ev_subevent_condense_step ev
        |  _ (vis ?ev _) _ _ => ev_subevent_condense_step ev
        | raiseOOM _ => setoid_rewrite Raise.raiseOOM_bind_itree
        | raiseUB _ => setoid_rewrite Raise.raiseUB_bind_itree
        | raise _ => setoid_rewrite Raise.raise_bind_itree
        | Ret _ => rewrite bind_ret_l
        end
  end
  .
  End InstrTactics.

  Import InstrTactics.
  Import InterpretationStack.
  Import LLVMAst.
  Require Import ZArith.

  (* RJS 10 Mar:
      1. Let's do symbolic stepping over the following instructions:
        Op
        Load
        Store
        Alloca
      
      2. Multi-instruction steps, i.e. if we have store-load,
       and the loaded pointer is no longer live, can we turn that into just the register value?

      3. A 'swap instruction' lemma along the lines of swapping two loads or a load and a store
       if they are of different memory locations and to different registers.
      
      4. denote_function: How do I say that two functions are equivalent for any input
        that is, they have the same set of external effects and the same return value,
        at the denote function level.
      
      5. cfg-mcfg link: To show that two functions are equivalent,
       should we be using interp_cfgn_exec, interp_cfgn, interp_mcfgn_exec, or interp_mcfgn?

      6. What would an alternate 'error-absorbing' interp for levels 4-6 look like that would allow us to always have a Ret,
        allowing Program Definition based approach to defining instruction rewriting lemmas. 
      
      *)
      Lemma eval_int_op_err_ub_oom_to_itree :
      forall {E} `{OOME -< E} `{FailureE -< E} `{UBE -< E} {I} `{VMI : VellvmIntegers.VMemInt I} `{DVI : ToDvalue I}
        x y iop,
        (@eval_int_op (itree E) I _ _ _ _ _ _ iop x y) ≈
          match eval_int_op iop x y with
          | ERR_UB_OOM (mkEitherT (mkEitherT (mkEitherT (mkIdent m)))) =>
              match m with
              | inl (OOM_message x) => raiseOOM x
              | inr (inl (UB_message x)) => raiseUB x
              | inr (inr (inl (ERR_message x))) => raise x
              | inr (inr (inr x)) => ret x
              end
          end.
    Proof.
      intros E H H0 H1 I VMI DVI x y iop.
      unfold eval_int_op.
      destruct iop; cbn; try reflexivity;
        try solve
          [ break_match; reflexivity
          | break_match; cbn; try reflexivity;
            unfold lift_OOM;
            break_inner_match; cbn;
            process;
            try reflexivity
          | break_match; cbn; try reflexivity;
            unfold lift_OOM;
            break_inner_match; cbn;
            process;
            try reflexivity;
            setoid_rewrite IP.VMemInt_intptr_dtyp;
            setoid_rewrite dtyp_eqb_refl;
            break_match; cbn; reflexivity
          ].
      - break_match; cbn; try reflexivity;
          unfold lift_OOM;
          break_inner_match; cbn;
          process; try reflexivity.
        repeat (break_match; cbn; try reflexivity);
          process; try reflexivity.
      - break_match; cbn; try reflexivity;
          unfold lift_OOM;
          break_inner_match; cbn;
          process; try reflexivity.
        repeat (break_match; cbn; try reflexivity);
          process; try reflexivity.
        repeat (break_match; cbn; try reflexivity);
          repeat rewrite bind_ret_l; try reflexivity;
          try discriminate.
        all: try (subst; cbn in *;
                  rewrite Heqb3;
                  inv Heqi1;
                  reflexivity).
        all: (repeat (break_match; cbn; try reflexivity);
              repeat setoid_rewrite Raise.raiseOOM_bind_itree; reflexivity).
      - break_match; cbn; try reflexivity;
          unfold lift_OOM;
          break_inner_match; cbn;
          process; try reflexivity.
        repeat (break_match; cbn; try reflexivity);
          process; try reflexivity.
      - break_match; cbn; try reflexivity;
          unfold lift_OOM;
          break_inner_match; cbn;
          process; try reflexivity.
        repeat (break_match; cbn; try reflexivity);
          process; try reflexivity.
      - break_match; cbn; try reflexivity;
          unfold lift_OOM;
          break_inner_match; cbn;
          process; try reflexivity.
        repeat (break_match; cbn; try reflexivity);
          process; try reflexivity.
    Qed.

  (* Note: we know that we can prove that [l = l'] is always true.
   However there is no reason to put this burden on the hypothesis, it is easier to use this way.
   Arguably we could do the same for [g] and [m] but haven't felt the need for it so far.
   *)
   (* Need to put the result of eval_int_op into the environment. *)
   (* Check interp_cfg2.
   Section dostuff.
    Variable u: @Integers.bit_int 64.
    Variable _id: raw_id.
    Variable les: local_env.
    Variable g: global_env.
    Check (Integers.repr 5).
      Check ((@eval_int_op _ _ _ _ _ _ _ _ (Add false true) u (Integers.repr 5%Z))).
      Check @eval_int_op.
      Locate eval_int_op.
      Check @eval_int_op.



Lemma interp3e_instr_op g les reg u  _id:
    (FMapAList.alist_find (Anon reg%Z) les) = Some (@UVALUE_I 64 u) ->
    (* contains_undef_or_poison u = false ->  *)
    eutt eq (interp_cfg2 (⟦ (IId _id,
                              INSTR_Op (OP_IBinop (LLVMAst.Add false true)
                                          (DynamicTypes.DTYPE_I 64) (EXP_Ident (ID_Local (Anon (reg)%Z))) (EXP_Integer (5)%Z))) ⟧i None) g les)
      (fmap (fun res => (FMapAList.alist_add _id (dvalue_to_uvalue res) les, (g, tt))) (@eval_int_op _ _ _ _ _ _ ((@VellvmIntegers.VIntVMemInt (@Integers.bit_int 64) (VellvmIntegers.VInt_Bounded 64))) _ (Add false true) u (Integers.repr 5%Z))).
   Proof.

  Check (fmap (fun res => (FMapAList.alist_add _id (dvalue_to_uvalue res) les, (g, tt))) (@eval_int_op (itree L2) _ _ _ _ _ _ _ (Add false true) u (Integers.repr 5%Z))). *)
  (* Import LLVMParamsBigIntptr.Events.DV.
  Import InterpreterStackBigIntptr.
  Import InterpreterStackBigIntptr.LLVM.
  Import InterpreterStackBigIntptr.LLVM.Local. *)
  Locate dvalue_to_uvalue.
  Locate eval_int_op.
  Locate interp_cfg2.

Lemma interp2_instr_op g les reg u _id:
    (FMapAList.alist_find (Anon reg%Z) les) = Some (@UVALUE_I 64 u) ->
    (* contains_undef_or_poison u = false ->  *)
    eutt eq (interp_cfg2 (⟦ (IId _id,
                              INSTR_Op (OP_IBinop (LLVMAst.Add false true)
                                          (DynamicTypes.DTYPE_I 64) (EXP_Ident (ID_Local (Anon (reg)%Z))) (EXP_Integer (5)%Z))) ⟧i None) g les)
      (fmap (fun res => (FMapAList.alist_add _id (dvalue_to_uvalue res) les, (g, tt))) (@eval_int_op _ _ _ _ _ _ ((@VellvmIntegers.VIntVMemInt (@Integers.bit_int 64) (VellvmIntegers.VInt_Bounded 64))) _ (Add false true) u (Integers.repr 5%Z))).
Proof.
  Local Opaque eval_int_op.
  intros Hfind .
  cbn.
  Ltac step :=  lazymatch goal with 
  | |- _ (interp_cfg2 (_ <- _ ;; _ ) _ _) _ => rewrite interp_cfg2_bind
  | |- _ (interp_cfg2 (translate _ (_ <- _ ;; _ )) _ _) _ => rewrite translate_bind
  | |- _ (_ <- (interp_cfg2 (_ <- _ ;; _ ) _ _);; _) _ => rewrite interp_cfg2_bind
  | |- _ (_ <- (interp_cfg2 (translate _ (_ <- _ ;; _ )) _ _);; _) _ => rewrite translate_bind
  | |- _ (_ <- (interp_cfg2 (translate _ (ITree.map _ _)) _ _);; _) _ => unfold ITree.map
  | |- _ (_ <- (interp_cfg2 (translate _ (Ret _)) _ _);; _) _ => rewrite translate_ret
  | |- _ (_ <- (interp_cfg2 (translate _ (raiseOOM _)) _ _);; _) _ => unfold raiseOOM; rewrite bind_trigger
  | |- _ (_ <- (interp_cfg2 (translate _ (raiseUB _)) _ _);; _) _  => unfold raiseUB; rewrite bind_trigger
  | |- _ (_ <- (interp_cfg2 (translate _ (raise _)) _ _);; _) _    => unfold raise; rewrite bind_trigger
  | |- _ (_ <- (interp_cfg2 (translate _ (vis _ _)) _ _);; _) _    => rewrite translate_vis
  | |- _ (_ <- (interp_cfg2 (vis _ _) _ _);; _) _    => rewrite interp_cfg2_vis
  | |- _ (_ <- (interp_cfg2 (Vis _ _) _ _);; _) _    => rewrite interp_cfg2_vis
  | |- _ (_ <- (interp_cfg2 (Ret _) _ _);; _) _ => rewrite interp_cfg2_ret
  | |- _ (_ <- (interp_cfg2 (translate _ (translate _ _)) _ _);; _) _ => go; cbn
  | |- _ (_ <- (interp_cfg2 (trigger (exp_to_instr _) ) _ _);; _) _ => unfold exp_to_instr; process
  | |- _ (_ <- (interp_cfg2 (trigger (LocalRead _) ) _ _);; _) _ => rewrite interp_cfg2_LR
  | |- _ (_ <- (_ <- _;; _) ;; _) _ => rewrite bind_bind
  | |- _ (_ <- (trigger _) ;; _) _ => rewrite bind_trigger
  | |- _ (_ <- (vis _ _) ;; _) _ => rewrite bind_vis
  | |- _ (_ <- (Ret _);; _) _ => rewrite bind_ret_l
  | |- _ => cbn
  end.
  repeat step.
  2: apply Hfind.
  cbn.
  repeat step.
  
  
  (* Local Opaque eval_iop. *)
  repeat rewrite eval_int_op_err_ub_oom_to_itree.
  remember (eval_int_op (Add false true) u (Integers.repr 5)) as x.
  destruct_err_ub_oom x.
  {
    repeat step. 
    process.
    setoid_rewrite interp_cfg2_OOM.
    repeat step.
    rewrite bind_trigger.
    rewrite bind_vis.
    eapply eqit_Vis.
    intros [].
  }

  { 
    repeat step.
    process.
    setoid_rewrite interp_cfg2_UB.
    repeat step.
    rewrite bind_trigger.
    rewrite bind_vis.
    eapply eqit_Vis.
    intros [].
  }

  { 
    repeat step.
    process.
    setoid_rewrite interp_cfg2_Err.
    repeat step.
    rewrite bind_trigger.
    rewrite bind_vis.
    eapply eqit_Vis.
    intros [].
  }
  repeat step.

  rewrite interp_cfg2_LW.
  cbn.
  rewrite bind_ret_l.
  reflexivity.
Qed.
Import VellvmRelations.
From ITree Require Import RuttFacts.


Definition instr_E_to_L0 {T : Type} : instr_E T -> itree L0 T :=
fun (e : instr_E T) =>
  match e with
  | inl1 call =>
      match call with
      | Call dt fv args =>
          raise "call"
      end
  | inr1 e0 =>
      trigger e0
  end.

Definition interp_instr_E_to_L0 :=
interp (@instr_E_to_L0).


    (* forall t, 
    (interp_cfg3 eq (⟦ (IId _id,
                              INSTR_Op (OP_IBinop (LLVMAst.Add false true)
                                          (DynamicTypes.DTYPE_I 64) (EXP_Ident (ID_Local (Anon (reg)%Z))) (EXP_Integer (5)%Z))) ⟧i None) g les sid mem
      ) t 
       <->
    (MEM_SPEC_INTERP.interp_memory_spec eq 
      (fmap (fun res => (FMapAList.alist_add _id (dvalue_to_uvalue res) les, (g, tt))) 
        (@eval_int_op _ _ _ _ _ _ ((@VellvmIntegers.VIntVMemInt (@Integers.bit_int 64) (VellvmIntegers.VInt_Bounded 64))) _ (Add false true) u (Integers.repr 5%Z))) sid mem
      ) t. *)
Lemma interp3_instr_op reg u  _id g les sid mem:
    (FMapAList.alist_find (Anon reg%Z) les) = Some (@UVALUE_I 64 u) ->
    (* contains_undef_or_poison u = false ->  *)
    refine_L3_cfg_eq (interp_cfg3 eq (⟦ (IId _id,
                              INSTR_Op (OP_IBinop (LLVMAst.Add false true)
                                          (DynamicTypes.DTYPE_I 64) (EXP_Ident (ID_Local (Anon (reg)%Z))) (EXP_Integer (5)%Z))) ⟧i None) g les sid mem
      ) (MEM_SPEC_INTERP.interp_memory_spec eq 
      (fmap (fun res => (FMapAList.alist_add _id (dvalue_to_uvalue res) les, (g, tt))) 
        (@eval_int_op _ _ _ _ _ _ ((@VellvmIntegers.VIntVMemInt (@Integers.bit_int 64) (VellvmIntegers.VInt_Bounded 64))) _ (Add false true) u (Integers.repr 5%Z))) sid mem
      ).
Proof.
  intros Hfind.
  eapply refine_23_cfg_eq.
  apply interp2_instr_op.
  eauto.
Qed.
Import DynamicTypes.
Print local_env.
Print raw_id.
Lemma interp3_instr_load _id g les sid mem:
 refine_L3_cfg_eq (interp_cfg3 eq (⟦ (IId  _id, (INSTR_Load (DTYPE_I 32) ((DTYPE_Pointer), (EXP_Ident (ID_Local (Anon (2)%Z)))) [ANN_align (4)%Z]))⟧i None) g les sid mem)
  (MEM_SPEC_INTERP.interp_memory_spec eq 
    (fmap (fun res => (FMapAList.alist_add _id (dvalue_to_uvalue res) les, (g, tt))) 
    (ret (DVALUE_None))) sid mem )
  .
Proof.
  simpl.
  unfold refine_L3_cfg_eq, refine_L3_cfg'.
  intros.
  eexists t'.
  split; try reflexivity.
  cbn.
  unfold interp_cfg3.
  setoid_rewrite interp_intrinsics_bind.
  


Admitted.
  (* Lemma denote_instr_load :
    forall (i : raw_id) volatile τ τp ptr align g l l' m a uv,
      ⟦ ptr at τp ⟧e3 g l m ≈ Ret3 g l' m (UVALUE_Addr a) ->
      read m a τ = inr uv ->
      ⟦ (IId i, INSTR_Load volatile τ (τp, ptr) align) '⟧ i3 g l m ≈ Ret3 g (Maps.add i uv l') m tt.
  Proof.
    intros * EXP READ.
    cbn.
    go.
    rewrite EXP.
    go.
    cbn.
    go.
    step.
    step.
    reflexivity.
  Qed. *)

  (* Lemma denote_instr_store : *)
  (*   forall {M} `{MemMonad MemState M} *)
  (*     (i : int) volatile τv val τp ptr align uv a g l l' l'' m m', *)
  (*     ⟦ val at τv ⟧e3 g l m ≈ Ret3 g l' m uv -> *)
  (*     ⟦ ptr at τp ⟧e3 g l' m ≈ Ret3 g l'' m (UVALUE_Addr a) -> *)
  (*     MemMonad_runs_to (write a uv τv) m = Some (m', tt) -> *)
  (*     ⟦ (IVoid i, INSTR_Store volatile (τv, val) (τp, ptr) align) ⟧i3 g l m ≈ Ret3 g l'' m' tt. *)
  (* Proof. *)
  (*   intros * EXP PTR WRITE. *)
  (*   cbn. *)
  (*   go. *)
  (*   rewrite EXP. *)
  (*   go. *)

  (*   go. *)
  (*   rewrite PTR. *)
  (*   go. *)
  (*   cbn. *)
  (*   go. *)
  (*   rewrite interp_cfg3_store; eauto. *)
  (*   reflexivity. *)
  (* Qed. *)

  (* Lemma denote_instr_store_exists : *)
  (*   forall (i : int) volatile τv val τp ptr align uv dv a g l l' l'' m aids, *)
  (*     ⟦ val at τv ⟧e3 g l m ≈ Ret3 g l' m uv -> *)
  (*     ⟦ ptr at τp ⟧e3 g l' m ≈ Ret3 g l'' m (UVALUE_Addr a) -> *)
  (*     uvalue_to_dvalue uv = inr dv -> *)
  (*     dvalue_has_dtyp dv τv -> *)
  (*     write_allowed (fst (ms_memory_stack m)) (fst a) (snd a) (N.to_nat (sizeof_dtyp τv)) = inr aids -> *)
  (*     exists m', *)
  (*       write (ms_memory_stack m) a dv = inr m' /\ ⟦ (IVoid i, INSTR_Store volatile (τv, val) (τp, ptr) align) ⟧i3 g l m ≈ Ret3 g l'' m' tt. *)
  (* Proof. *)
  (*   intros * EXP PTR CONV_UV TYP FITS. *)
  (*   apply write_succeeds with (v:=dv) in FITS as [m2 WRITE]; auto. *)
  (*   exists m2. split; auto. *)
  (*   eapply denote_instr_store; eauto. *)
  (* Qed. *)

  (* Lemma denote_instr_alloca_exists : *)
  (*   forall m τ g l i align nb, *)
  (*     non_void τ -> *)
  (*     exists m' a, *)
  (*       allocate m τ = inr (m', a) /\ *)
  (*       ⟦ (IId i, INSTR_Alloca τ nb align) ⟧i3 g l m ≈ Ret3 g (Maps.add i (UVALUE_Addr a) l) m' tt. *)
  (* Proof. *)
  (*   intros * NV. *)
  (*   pose proof interp_cfg3_alloca m τ g l NV as (m' & a & ALLOC & TRIGGER). *)
  (*   exists m', a. split; auto. *)

  (*   cbn. go.  *)
  (*   rewrite TRIGGER; cbn. *)
  (*   rewrite bind_ret_l. *)
  (*   step; reflexivity. *)
  (* Qed. *)

  (* Lemma denote_instr_comment : *)
  (*   forall i str g l m, *)
  (*     ⟦ (IVoid i, INSTR_Comment str) ⟧i3 g l m ≈ Ret3 g l m tt. *)
  (* Proof. *)
  (*   intros *. *)
  (*   destruct i; cbn; go; reflexivity. *)
  (* Qed. *)

  (* Lemma denote_instr_op : *)
  (*   forall i op uv g l l' m, *)
  (*     ⟦ op ⟧e3 g l m ≈ Ret3 g l' m uv -> *)
  (*     ⟦ (IId i, INSTR_Op op) ⟧i3 g l m ≈ Ret3 g (Maps.add i uv l') m tt. *)
  (* Proof. *)
  (*   intros * OP. *)
  (*   cbn. *)
  (*   unfold denote_op. *)
  (*   go. *)
  (*   rewrite OP. *)
  (*   go; step; reflexivity. *)
  (* Qed. *)

  (* Lemma denote_instr_gep_array : *)
  (*   forall i size τ e_ix ix ptr a val g l l' l'' m, *)
  (*     ⟦ ptr at DTYPE_Pointer ⟧e3 g l m ≈ Ret3 g l' m (UVALUE_Addr a) *)
  (*     -> *)
  (*     ⟦ e_ix at DTYPE_I 64 ⟧e3 g l' m ≈ Ret3 g l'' m (UVALUE_I64 (repr (Z.of_nat ix))) *)
  (*     -> *)
  (*     get_array_cell m a ix τ = inr val *)
  (*     -> *)
  (*     exists ptr_res, *)
  (*       read m ptr_res τ = inr val /\ *)
  (*       ⟦ (IId i, INSTR_Op (OP_GetElementPtr (DTYPE_Array size τ) (DTYPE_Pointer, ptr) [(DTYPE_I 64, EXP_Integer 0%Z); (DTYPE_I 64, e_ix)])) ⟧i3 g l m *)
  (*       ≈ *)
  (*       Ret3 g (Maps.add i (UVALUE_Addr ptr_res) l'') m tt.  *)
  (* Proof. *)
  (*   intros * PTR IX GET. *)

  (*   pose proof interp_cfg3_GEP_array τ a size g l'' m val ix GET as (ptr_res & EQ & READ). *)
  (*   exists ptr_res. split; auto. *)

  (*   cbn. *)
  (*   go. *)
  (*   rewrite PTR. *)
  (*   go. *)
  (*   rewrite !bind_bind. *)
  (*   rewrite IX; cbn. *)
  (*   go. *)
  (*   cbn. *)
  (*   unfold ITree.map. *)
  (*   go. *)
  (*   rewrite EQ. *)
  (*   go. *)
  (*   step. *)
  (*   reflexivity. *)
  (* Qed. *)

  (* Lemma denote_instr_gep_array' : *)
  (*   forall i size τ e_ix ix ptr a val g l l' l'' m, *)
  (*     ⟦ ptr at DTYPE_Pointer ⟧e3 g l m ≈ Ret3 g l' m (UVALUE_Addr a) *)
  (*     -> *)
  (*     ⟦ e_ix at DTYPE_I 64 ⟧e3 g l' m ≈ Ret3 g l'' m (UVALUE_I64 (repr (Z.of_nat ix))) *)
  (*     -> *)
  (*     get_array_cell m a ix τ = inr val *)
  (*     -> *)
  (*     exists ptr_res, *)
  (*       read m ptr_res τ = inr val /\ *)
  (*       handle_gep_addr (DTYPE_Array size τ) a [DVALUE_I64 (repr 0); DVALUE_I64 (repr (Z.of_nat ix))] = inr ptr_res /\ *)
  (*       ⟦ (IId i, INSTR_Op (OP_GetElementPtr (DTYPE_Array size τ) (DTYPE_Pointer, ptr) [(DTYPE_I 64, EXP_Integer 0%Z); (DTYPE_I 64, e_ix)])) ⟧i3 g l m *)
  (*       ≈ *)
  (*       Ret3 g (Maps.add i (UVALUE_Addr ptr_res) l'') m tt. *)
  (* Proof. *)
  (*   intros * PTR IX GET. *)

  (*   pose proof interp_cfg3_GEP_array' τ a size g l'' m val ix GET as (ptr_res & EQ & GEP & READ). *)
  (*   exists ptr_res. *)
  (*   split; auto. *)
  (*   split; auto. *)

  (*   cbn. *)
  (*   go. *)
  (*   rewrite !bind_bind. *)
  (*   rewrite PTR. *)
  (*   go. *)
  (*   rewrite IX. *)
  (*   go. *)
  (*   cbn; unfold ITree.map. *)
  (*   go. *)
  (*   rewrite EQ. *)
  (*   go. *)
  (*   step. *)
  (*   reflexivity. *)
  (* Qed. *)

  (* Lemma denote_instr_gep_array_no_read_addr : *)
  (*   forall i size τ e_ix ix ptr a g l l' l'' m ptr_res, *)
  (*     ⟦ ptr at DTYPE_Pointer ⟧e3 g l m ≈ Ret3 g l' m (UVALUE_Addr a) *)
  (*     -> *)
  (*     ⟦ e_ix at DTYPE_I 64 ⟧e3 g l' m ≈ Ret3 g l'' m (UVALUE_I64 (repr (Z.of_nat ix))) *)
  (*     -> *)
  (*     dtyp_fits m a (DTYPE_Array size τ) -> *)
  (*     handle_gep_addr (DTYPE_Array size τ) a [DVALUE_I64 (Int64.repr 0); DVALUE_I64 (Int64.repr (Z.of_nat ix))] = inr ptr_res -> *)
  (*     ⟦ (IId i, INSTR_Op (OP_GetElementPtr (DTYPE_Array size τ) (DTYPE_Pointer, ptr) [(DTYPE_I 64, EXP_Integer 0%Z); (DTYPE_I 64, e_ix)])) ⟧i3 g l m *)
  (*     ≈ *)
  (*     Ret3 g (Maps.add i (UVALUE_Addr ptr_res) l'') m tt.  *)
  (* Proof. *)
  (*   intros * PTR IX FITS HGEP. *)
  (*   pose proof @interp_cfg3_GEP_array_no_read_addr τ a size g l'' m ix ptr_res FITS. *)

  (*   cbn. *)
  (*   go. *)
  (*   rewrite PTR. *)
  (*   go. *)
  (*   rewrite IX. *)
  (*   go. *)
  (*   cbn; unfold ITree.map; go. *)
  (*   rewrite H; auto. *)
  (*   go. *)
  (*   step. *)
  (*   reflexivity. *)
  (* Qed. *)

  (* Lemma denote_instr_gep_array_no_read : *)
  (*   forall i size τ e_ix ix ptr a g l l' l'' m, *)
  (*     ⟦ ptr at DTYPE_Pointer ⟧e3 g l m ≈ Ret3 g l' m (UVALUE_Addr a) *)
  (*     -> *)
  (*     ⟦ e_ix at DTYPE_I 64 ⟧e3 g l' m ≈ Ret3 g l'' m (UVALUE_I64 (repr (Z.of_nat ix))) *)
  (*     -> *)
  (*     dtyp_fits m a (DTYPE_Array size τ) -> *)
  (*     exists ptr_res, *)
  (*       handle_gep_addr (DTYPE_Array size τ) a [DVALUE_I64 (repr 0); DVALUE_I64 (repr (Z.of_nat ix))] = inr ptr_res /\ *)
  (*       ⟦ (IId i, INSTR_Op (OP_GetElementPtr (DTYPE_Array size τ) (DTYPE_Pointer, ptr) [(DTYPE_I 64, EXP_Integer 0%Z); (DTYPE_I 64, e_ix)])) ⟧i3 g l m *)
  (*       ≈ *)
  (*       Ret3 g (Maps.add i (UVALUE_Addr ptr_res) l'') m tt. *)
  (* Proof. *)
  (*   intros * PTR IX FITS. *)

  (*   pose proof interp_cfg3_GEP_array_no_read τ a size g l'' m ix FITS as (ptr_res & EQ & GEP). *)
  (*   exists ptr_res. *)
  (*   split; auto. *)

  (*   cbn. *)
  (*   go. *)
  (*   rewrite PTR. *)
  (*   go. *)
  (*   rewrite IX. *)
  (*   unfold ITree.map; cbn. *)
  (*   go. *)
  (*   cbn. *)
  (*   go. *)
  (*   rewrite EQ. *)
  (*   go. *)
  (*   step; reflexivity. *)
  (* Qed. *)

  (* Lemma denote_instr_intrinsic : *)
  (*   forall i τ fn in_n sem_f args arg_vs conc_args res g l m, *)
  (*     @intrinsic_exp dtyp (EXP_Ident (ID_Global (Name fn))) = Some in_n *)
  (*     -> *)
  (*     assoc in_n (defs_assoc) = Some sem_f *)
  (*     -> *)
  (*     ℑ3 (map_monad (fun '(t, op) => translate exp_to_instr ⟦ op at t ⟧e) args) g l m *)
  (*     ≈ *)
  (*     Ret3 g l m arg_vs *)
  (*     -> *)
  (*     ℑ3 (map_monad (fun uv : uvalue => pickUnique uv) arg_vs) g l m *)
  (*     ≈ *)
  (*     Ret3 g l m conc_args *)
  (*     -> *)
  (*     sem_f conc_args = inr res *)
  (*     -> *)
  (*     ⟦ (IId i, INSTR_Call (τ, EXP_Ident (ID_Global (Name fn))) args) ⟧i3 g l m *)
  (*     ≈ *)
  (*     Ret3 g (FMapAList.alist_add i (dvalue_to_uvalue res) l) m tt. *)
  (* Proof. *)
  (*   intros * INTRINSIC ASSOC MAP CONCARGS RES. *)

  (*   cbn. *)
  (*   go. *)
  (*   rewrite MAP. *)
  (*   go. *)
  (*   cbn in *. *)
  (*   rewrite INTRINSIC. *)
  (*   go. *)
  (*   rewrite CONCARGS. *)
  (*   unfold ITree.map; go. *)
  (*   rewrite interp_cfg3_intrinsic; eauto. *)
  (*   go. *)
  (*   step. *)
  (*   reflexivity. *)
  (* Qed. *)

  (* Lemma denote_term_br_l : *)
  (*   forall (e : exp dtyp) b1 b2 g l l' m, *)
  (*     ⟦ e at DTYPE_I 1 ⟧e3 g l m ≈ Ret3 g l' m (UVALUE_I1 one) -> *)
  (*     ⟦ TERM_Br (DTYPE_I 1%N, e) b1 b2 ⟧t3 g l m ≈ Ret3 g l' m (inl b1). *)
  (* Proof. *)
  (*   intros * EXP. *)
  (*   simpl. *)
  (*   go. *)
  (*   rewrite EXP; go. *)
  (*   cbn. *)
  (*   go. *)
  (*   cbn. *)
  (*   go. *)
  (*   reflexivity. *)
  (* Qed. *)

  (* Lemma denote_term_br_r : *)
  (*   forall (e : exp dtyp) b1 b2 g l l' m, *)
  (*     ⟦ e at DTYPE_I 1 ⟧e3 g l m ≈ Ret3 g l' m (UVALUE_I1 zero) -> *)
  (*     ⟦ TERM_Br (DTYPE_I 1%N, e) b1 b2 ⟧t3 g l m ≈ Ret3 g l' m (inl b2). *)
  (* Proof. *)
  (*   intros * EXP. *)
  (*   simpl. *)
  (*   go. *)
  (*   rewrite EXP; go. *)
  (*   cbn. *)
  (*   go. *)
  (*   cbn. *)
  (*   go. *)
  (*   reflexivity. *)
  (* Qed. *)

  (* Lemma denote_term_br_1 : *)
  (*   forall b g l m, *)
  (*     ⟦ TERM_Br_1 b ⟧t3 g l m ≈ Ret3 g l m (inl b). *)
  (* Proof. *)
  (*   intros b g ρ m. *)
  (*   cbn. *)
  (*   go. *)
  (*   reflexivity. *)
  (* Qed. *)
End InstrLemmas.
