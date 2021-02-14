(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

From Coq Require Import
     ZArith Ascii Strings.String Setoid Morphisms List.

From ITree Require Import
     ITree
     Basics.HeterogeneousRelations
     Eq.Eq
     Interp.Interp
     Interp.InterpFacts
     Interp.TranslateFacts
     Basics.MonadState
     Events.StateFacts.

From Vellvm Require Import
     Error
     Util
     LLVMAst
     AstLib
     CFG
     DynamicTypes
     DynamicValues
     Denotation
     Handlers.Handlers
     LLVMEvents
     Transformations.Transformation
     Traversal
     TopLevelRefinements.

From ExtLib Require Import
     Programming.Eqv
     Structures.Monads.

Import EqvNotation.

Open Scope Z_scope.
Open Scope string_scope.

From Vellvm Require Import
     AstLib.
Import ListNotations.

Import DV.
Import R.

Import MonadNotation.

Section Swap.

  (* Class Swap (A:Type) := swap : raw_id -> raw_id -> A -> A. *)

  Variable id1 id2: raw_id.

  Definition swap_raw_id (id:raw_id) : raw_id :=
    if id ~=? id1 then id2 else
      if id ~=? id2 then id1 else
        id.

  Instance swap_endo_raw_id : Endo raw_id := swap_raw_id.

  Definition swap_mcfg: transformation := endo.
  Definition swap_dmcfg: Endo (mcfg dtyp) := endo.

  (*
    For now we forget about normalization of types, we reason after it happened.
    I'll see how to plug it back in the story later.
  Lemma normalize_types_swap: forall p,
      normalize_types (swap_mcfg p) = swap_dmcfg (normalize_types p).
  Proof.
  Admitted.
   *)
  Ltac split_bind := apply eutt_clo_bind with (UU := Logic.eq); [| intros ? (? & ? & ?) ->].

  (** Logical relation for the [list] type. *)
  Inductive list_rel {A1 A2 : Type}
            (RA : A1 -> A2 -> Prop) : (list A1) -> (list A2) -> Prop :=
  | list_rel_nil: list_rel RA [] []
  | list_rel_cons: forall a1 a2 tl1 tl2, RA a1 a2 -> list_rel RA tl1 tl2 -> list_rel RA (a1 :: tl1) (a2 :: tl2)
  .
  Hint Constructors list_rel : core.

  (* In top-level, [address_one_function] is mapped to return notably a mapping from function addresses to itrees.
     We hence want to get extensional eutt over the returned type.
   *)
  Definition function_rel {X}:
    relation (FMapAList.alist raw_id uvalue * @Stack.stack X * (FMapAList.alist raw_id dvalue * list (uvalue * (list uvalue -> itree L0 uvalue)))) := (Logic.eq × (Logic.eq × list_rel (refine_uvalue × (fun d1 d2 => forall x, eutt refine_uvalue (d1 x) (d2 x))))).
  Hint Unfold function_rel : core.

  Global Instance list_rel_refl {R: Type} {RR: relation R} `{Reflexive _ RR} : Reflexive (list_rel RR).
  Proof.
    intros l; induction l as [| hd tl IH]; auto.
  Qed.

  Global Instance function_rel_refl {X}: Reflexive (@function_rel X).
  Proof.
    repeat apply prod_rel_refl; auto.
    eapply list_rel_refl.
    Unshelve.
    apply prod_rel_refl; auto. apply refine_uvalue_Reflexive.
    intros ? ?.
    reflexivity.
  Qed.

  (*
  (* Calvin broke this somehow by changing uvalue to not include
     CallE. Yannick promises not to be mad later when fixing this. :) *)
  Lemma interp2_map_monad: forall {X} (f: X -> itree _ (uvalue * D.function_denotation)) (g: endo X) (l: list X) s1 s2,
      (forall x s1 s2, In x l -> eutt (Logic.eq × (Logic.eq × (refine_uvalue × (fun d1 d2 => forall x, eutt refine_uvalue (d1 x) (d2 x))))) (interp2 nil (f x) s1 s2) (interp2 nil (f (g x)) s1 s2)) ->
      eutt function_rel (interp2 nil (map_monad f l) s1 s2) (interp2 nil (map_monad f (map g l)) s1 s2).
  Proof.
    induction l as [| x l IH]; simpl; intros; [reflexivity |].
    rewrite 2 interp2_bind.
    eapply eutt_clo_bind; eauto.
    intros (? & ? & ? & ?) (? & ? & ? & ?) EQ.
    repeat match goal with | h: prod_rel _ _ _ _ |- _ => inv h end.
    rewrite 2 interp2_bind.
    eapply eutt_clo_bind; eauto.
    intros (? & ? & ?) (? & ? & ?) EQ.
    inv EQ.
    repeat match goal with | h: prod_rel _ _ _ _ |- _ => inv h end.
    rewrite 2 interp2_ret.
    apply eqit_Ret.
    constructor; auto.
  Qed.
  *)

  Lemma swap_correct_L2:
    forall dt entry args intrinsics p, refine_mcfg_L2 dt entry args intrinsics p (swap_mcfg p).
  Proof.
    intros p.
    unfold refine_mcfg_L2.
    unfold model_to_L2.

    (* unfold denote_vellvm. *)
    (* unfold denote_vellvm_init. *)
    (* unfold denote_vellvm. *)
    (* simpl; rewrite 2 interp2_bind. *)
    (* split_bind. *)

    {
      (* Reasoning about initialization *)
      admit.
    }
Admitted.
(*     rewrite 2 interp2_bind. *)
(*     (* We use [function_rel] here to establish that we get piece-wise eutt when denoting each function *) *)
(*     eapply eutt_clo_bind with function_rel. *)
(*     Focus 2. *)
(*     intros u1 u2 H. *)
(*     epose proof function_rel. *)
(*     unfold D.function_denotation in *. *)
(*     { *)
(*       (* Denotation of each cfg *) *)
(*       (* Here we need to actually establish something different than equality of states, but rather extensional agreement after renaming *) *)
(*       apply interp2_map_monad. *)
(*       intros cfg g l HIN. *)
(*       unfold address_one_function. *)
(*       simpl. *)
(*       rewrite 2 interp2_bind. *)
(*       split_bind. *)
(*       { (* Getting the address of the function *) *)
(*         admit. *)
(*       } *)
(*       rewrite 2 interp2_ret. *)
(*       apply eqit_Ret. *)
(*       do 3 constructor; auto. *)
(*       intros args. *)
(*       destruct cfg. *)
(*       unfold f_endo, endo_definition; simpl. *)
(*       unfold D.denote_function. *)
(*       simpl. *)
(*       apply eutt_clo_bind with (UU := Logic.eq). *)
(*       (* Debug message, to remove / deal with *) *)
(*       admit. *)
(*       intros ? ? ->. *)
(*       apply eutt_clo_bind with (UU := Logic.eq); [reflexivity | intros [] [] _]. *)
(*       apply eutt_clo_bind with (UU := Logic.eq); [reflexivity | intros [] [] _]. *)
(*       apply eutt_clo_bind with (UU := Logic.eq); [| intros ? ? ->; reflexivity]. *)
(*       apply eutt_translate'. *)

(*       unfold D.denote_cfg. *)
(* (* *)
(*       Set Nested Proofs Allowed. *)
(*       Lemma denote_cfg_comp: *)
(*         forall  {E} (body body': (block_id + block_id) -> itree E (block_id + block_id)) (x: block_id) (f: endo block_id), *)
(*           (forall l, body l ≈ body' (f l)) -> *)
(*           loop body x ≈ loop body' (f x). *)

(*       unfold D.denote_cfg. *)
(*       unfold f_endo. endo_cfg. simpl. *)
(*       unfold eqm. *)
(*       Instance loop_Proper: *)
(*         Proper () loop *)
(*       (* Set Printing Implicit. *) *)
(*       apply (@Proper_loop. *)
(* *) *)

(*       admit. *)

(*     } *)

(*     intros (? & ? & ?) (? & ? & ?) EQ. *)
(*     inv EQ; repeat match goal with | h: prod_rel _ _ _ _ |- _ => inv h end. *)
(*     rewrite 2 interp2_bind. *)
(*     split_bind. *)

(*     { (* Getting the address of "main" *) *)
(*       admit. *)
(*     } *)

(*     (* Tying the recursive knot *) *)

(*     admit. *)
(*   (*   rewrite 2 interp2_bind. *) *)


(*   (*   2:rewrite interp2_bind; reflexivity. *) *)
(*   (*   unfold f_endo, endo_list. *) *)
(*   (*   apply interp2_map_monad. *) *)
(*   (*   intros. *) *)
(*   (*   remember (interp2 (address_one_function x) s1 s2). *) *)
(*   (*   cbn. *) *)
(*   (*   rewrite 2 interp2_bind. *) *)
(*   (*   split_bind. *) *)
(*   (*   { (* Reading the name of the function *) *) *)
(*   (*     admit. *) *)
(*   (*   } *) *)

(*   (*     unfold f_endo. *) *)
(*   (*     Set Printing All. *) *)
(*   (*     unfold interp2, INT.interpret_intrinsics, interp_global, interp_local_stack. *) *)
(*   (*     rewrite interp_trigger; cbn. *) *)
(*   (*     Lemma refine_cfg_to_mcfg: forall {B} f (l:list (definition dtyp (cfg dtyp))) s1 s2, *) *)
(*   (*       interp2 (map_monad (B := B) f l) s1 s2 = *) *)
(*   (*       interp2 (map_monad f l) s1 s2. *) *)

(*   (*     (* Denotation of each cfg, need a modularity lemma *) *) *)



(*   (*   { *) *)
(*   (*     Transparent build_global_environment. *) *)
(*   (*     unfold build_global_environment. *) *)
(*   (*     simpl. *) *)
(*   (*     rewrite interp_intrinsics_bind, interp_global_bind, build_L2_bind. *) *)
(*   (*     setoid_rewrite interp_intrinsics_bind. *) *)
(*   (*     setoid_rewrite interp_global_bind. *) *)
(*   (*     setoid_rewrite build_L2_bind. *) *)
(*   (*     eapply eutt_clo_bind with (UU := Logic.eq). *) *)
(*   (*     { *) *)
(*   (*       match goal with |- _ ≈ run_state ?m ?s => rewrite <- (bind_ret2 (run_state m s)) end. *) *)
(*   (*       eapply eutt_clo_bind. *) *)
(*   (*       2: intros [] [] *) *)
(*   (*     } *) *)
(*   (*     intros ? (? & ? & ?) ?; subst. *) *)
(*   (*     eapply eutt_refine_L2_proper. *) *)
(*   (*     eapply eqitgen_cong_eqit_eq; [| reflexivity |]. *) *)
(*   (*     setoid_rewrite interp_global_bind. *) *)
(*   (*     do 2 setoid_rewrite build_L2_bind. *) *)


(*   (*   unfold normalize_types, eval_typ; cbn. *) *)
(*   (*   unfold swap_mcfg, f_endo, endo_mcfg; cbn. *) *)
(*   (*   unfold fmap_mcfg, fmap_modul; cbn. *) *)
(*   (*   unfold swap_dmcfg, f_endo, endo_mcfg; cbn. *) *)
(*   (*   f_equal. *) *)
(*   (*   - unfold f_endo, endo_list. *) *)
(*   (*     induction m_type_defs as [| [] tl IH]; [reflexivity | cbn]. *) *)
(*   (*     f_equal. *) *)
(*   (*     unfold f_endo, endo_id. *) *)

(*   (*     P: mcfg typ -> Prop := fun p => refine_mcfg_L2 p (endo_mcfg p). *) *)
(*   (*     goal: forall p, P p. *) *)

(*   (*     rewrite map_map. *) *)
(*   (*     f_equal. *) *)
(*   (*     2: rewrite <- IH. *) *)
(*   (*   - *) *)
(*   (*   unfold normalize_types, eval_typ. *) *)
(*   (*   cbn. *) *)
(*   (*   (* unfold swap_mcfg, f_endo, endo_mcfg. *) *) *)
(*   (*   f_endo, endo_option. *) *)

(*   (*   destruct p as [a b c d e f g]. *) *)

(*   (*   destruct m_globals, m_definitions, m_declarations. *) *)

(*   (* Lemma swap_correct_L2: *) *)
(*   (*   forall p, refine_mcfg_L2 p (swap_mcfg p). *) *)
(*   (* Proof. *) *)
(*   (*   intros p. *) *)
(*   (*   unfold refine_mcfg_L2. *) *)
(*   (*   unfold build_to_L2. *) *)

(*   (*   Opaque build_uvalue. *) *)
(*   (*   cbn. *) *)

(*   (*   cbn. *) *)

(*   Admitted. *)

  Theorem swap_cfg_correct: transformation_correct swap_mcfg.
  Proof.
    unfold transformation_correct.
    intros dt entry args intrinsics m. 
    apply refine_mcfg_L2_correct, swap_correct_L2.
  Qed.

  (* YZ: TEMPORARY TESTING, TO REMOVE AFTERWARDS *)
  (*
  (* Here's some random cfg *)
  Definition foo :=
    {|
      init := Anon 0%Z;
      blks := [{|
                  blk_id := Anon 0%Z;
                  blk_phis := [];
                  blk_code := [(IId (Anon 1%Z),
                                INSTR_Op
                                  (OP_IBinop (Add false false) (TYPE_I 32%Z) (EXP_Integer 5%Z) (EXP_Integer 9%Z)));
                                 (IId (Anon 2%Z),
                                  INSTR_Op
                                    (OP_IBinop (Add false false) (TYPE_I 32%Z) (EXP_Ident (ID_Local (Anon 1%Z)))
                                               (EXP_Integer 15%Z)))];
                  blk_term := (IVoid 0%Z, TERM_Ret (TYPE_I 32%Z, EXP_Ident (ID_Local (Anon 2%Z))));
                  blk_comments := None |}];
      args := [ID_Local (Name "argc"); ID_Local (Name "arcv")] |}.

    (* We can define a generic endomorphism that will do the traversal without altering anything *)
    Definition dummy_swap_cfg: endo (cfg typ) := f_endo.
    (* And it does indeed do nothing *)
    Eval compute in dummy_swap_cfg foo.

    (* But now let's simply hijack the endomorphism for [raw_id] by declaring a local instance of [endo] *)
    Variable id1 id2: raw_id.
    Instance swap_endo_raw_id : endo raw_id := swap_raw_id id1 id2.
    (* And still rely on type classes to define the swap at the level of cfgs *)
    Definition swap_cfg: endo (cfg typ) := f_endo.

    (* We now get an [endo] that does the substitution in the leaves (albeit not concretely here since of course since [id1] and [id2] are not instantiated *)
    Eval compute in swap_cfg foo.

  (* Note however that we _need_ to fix [id1] and [id2] as variables, the following does not work:

     Instance swap_endo_raw_id (id1 id2: raw_id): endo raw_id := swap_raw_id id1 id2.
     Definition swap_cfg (id1 id2: raw_id): endo (cfg typ) := f_endo.

   *)
   *)

End Swap.


(** WIP: ELEMENTS OF PROOF TO PLUG BACK UP THERE.
 *)
(*
(** We define a renaming pass and prove it correct.
    The basic operation consider is a _swap_ between two [raw_id].
 *)

Module RENAMING
       (A:MemoryAddress.ADDRESS)
       (LLVMEvents:LLVM_INTERACTIONS(A)).

  Module SS := Denotation A LLVMEvents.
  Import SS.
  Import LLVMEvents.

  (******************** Type classes ********************)

  (* Swap operation *)
  Class Swap (A:Type) := swap : raw_id -> raw_id -> A -> A.

  Class SwapLaws (A:Type) `{Swap A} :=
    {
      (* Swapping a variable for itself is the identity. *)
      swap_same_id :
        forall (id:raw_id) (x:A), swap id id x = x;

      (* [swap] is commutative *)
      swap_comm:
        forall id1 id2 (x:A), swap id1 id2 x = swap id2 id1 x;

      (* [swap] is idempotent *)
      swap_swap_id :
        forall id1 id2 (x:A), swap id1 id2 (swap id1 id2 x) = x
    }.

  (* Particular case where [swap] is [id] *)
  Class SwapInvariant (A:Type) `{Swap A} :=
    {
      swap_invariant :
        forall id1 id2 (x:A), swap id1 id2 x = x
    }.

  (******************** Swap instances ********************)

  (******************** Syntactic swaps ********************)

  Definition swap_raw_id (id1 id2:raw_id) (id:raw_id) : raw_id :=
    if id ~=? id1 then id2 else
      if id ~=? id2 then id1 else
        id.
  Instance swap_of_raw_id : Swap raw_id := swap_raw_id.
  Hint Unfold swap_of_raw_id.

  Ltac unfold_swaps :=
    repeat match goal with
           | [H : context [swap _ _ _] |- _] => unfold swap in H; autounfold in H
           | [H : _ |- context[swap _ _ _] ] => unfold swap; autounfold
           end.

  Ltac simpl_ifs :=
    repeat match goal with
           | [_ : context [if ?X then _ else _] |- _] => destruct (X)
           | [_ : _ |- context [if ?X then _ else _ ]] => destruct (X)
           end.

  Program Instance raw_id_swaplaws : SwapLaws raw_id.
  Next Obligation.
    unfold_swaps. unfold swap_raw_id.
    destruct (x ~=? id); auto.
  Qed.
  Next Obligation.
    unfold_swaps. unfold swap_raw_id. simpl_ifs; subst; auto.
    unfold eqv, eqv_raw_id in *. subst. reflexivity.
  Qed.
  Next Obligation.
    unfold_swaps. unfold swap_raw_id. simpl_ifs; subst; unfold eqv, eqv_raw_id in *; subst; auto.
    - contradiction.
    - contradiction.
    - contradiction.
    - contradiction.
  Qed.

  Definition swap_ident (id1 id2:raw_id) (id:ident) : ident :=
    match id with
    | ID_Global i => ID_Global (swap id1 id2 i)
    | ID_Local i => ID_Local (swap id1 id2 i)
    end.
  Instance swap_of_ident : Swap ident := swap_ident.
  Program Instance ident_swaplaws : SwapLaws ident.
  Next Obligation.
    unfold_swaps; unfold swap_of_ident; destruct x; simpl; rewrite swap_same_id; reflexivity.
  Qed.
  Next Obligation.
    unfold_swaps; unfold swap_of_ident; destruct x; simpl; rewrite swap_comm; reflexivity.
  Qed.
  Next Obligation.
    unfold_swaps; unfold swap_of_ident; destruct x; simpl; rewrite swap_swap_id; reflexivity.
  Qed.

  Instance swap_of_pair {A B} `(SA:Swap A) `(SB:Swap B) : Swap (A * B)%type :=
    fun id1 id2 '(a,b) => (swap id1 id2 a, swap id1 id2 b).
  Hint Unfold swap_of_pair.

  Program Instance swap_laws_pair {A B} `(SA:Swap A) `(SB:Swap B) `(SLA:SwapLaws A) `(SLB:SwapLaws B) : SwapLaws (A*B)%type.
  Next Obligation.
    unfold swap. unfold swap_of_pair.
    rewrite swap_same_id. rewrite swap_same_id. reflexivity.
  Qed.
  Next Obligation.
    unfold swap. unfold swap_of_pair. simpl.
    rewrite swap_comm. rewrite (@swap_comm B) at 1. reflexivity. assumption.
  Qed.
  Next Obligation.
    unfold swap. unfold swap_of_pair. simpl.
    rewrite swap_swap_id. rewrite (@swap_swap_id B) at 1. reflexivity. assumption.
  Qed.

  Instance swap_of_option {A} `(SA:Swap A) : Swap (option A) :=
    fun id1 id2 opt => match opt with None => None | Some x => Some (swap id1 id2 x) end.
  Hint Unfold swap_of_option.

  Instance swap_of_list {A} `(SA:Swap A) : Swap (list A) :=
    fun id1 id2 l => List.map (swap id1 id2) l.
  Hint Unfold swap_of_list.

  Instance swap_of_err {A} `(SA:Swap A) : Swap (err A) :=
    fun id1 id2 e =>
      match e with
      | inl s => inl s
      | inr a => inr (swap id1 id2 a)
      end.
  Hint Unfold swap_of_err.

  Instance swap_of_bool : Swap bool :=
    fun id1 id2 b => b.

  Instance swap_of_nat : Swap nat :=
    fun id1 id2 n => n.

  Instance swap_of_int : Swap int :=
    fun id1 id2 n => n.

  Instance swap_of_string : Swap string :=
    fun id1 id2 s => s.

  Instance swap_of_ibinop : Swap ibinop :=
    fun id1 id2 n => n.

  Instance swap_of_fbinop : Swap fbinop :=
    fun id1 id2 n => n.

  Instance swap_of_icmp : Swap icmp :=
    fun id1 id2 n => n.

  Instance swap_of_fcmp : Swap fcmp :=
    fun id1 id2 n => n.

  Hint Unfold swap_of_bool swap_of_nat swap_of_string swap_of_int swap_of_ibinop swap_of_fbinop swap_of_icmp swap_of_fcmp.

  Fixpoint swap_typ (id1 id2:raw_id) (t:typ) : typ :=
    match t with
    | TYPE_Pointer t' => TYPE_Pointer (swap_typ id1 id2 t')
    | TYPE_Array sz t' => TYPE_Array sz (swap_typ id1 id2 t')
    | TYPE_Function ret args => TYPE_Function (swap_typ id1 id2 ret) (List.map (swap_typ id1 id2) args)
    | TYPE_Struct fields => TYPE_Struct (List.map (swap_typ id1 id2) fields)
    | TYPE_Packed_struct fields => TYPE_Packed_struct (List.map (swap_typ id1 id2) fields)
    | TYPE_Vector sz t' => TYPE_Vector sz (swap_typ id1 id2 t')
    | TYPE_Identified id => TYPE_Identified (swap id1 id2 id)
    | _ => t
    end.
  (* Hint Unfold swap_typ.*) (* DO WE WANT THESE UNFOLD HINTS? *)

  Instance swap_of_typ : Swap typ := swap_typ.
  Hint Unfold swap_of_typ.

  Instance swap_of_dtyp : Swap dtyp :=
    fun id1 id2 d => d.

  Section WithT.
    Variable T:Set.
    Context `{ST: Swap T}.

    Global Instance swap_of_tident : Swap tident := swap.
    Hint Unfold swap_of_tident.

    Fixpoint swap_exp (id1 id2:raw_id) (e:exp T) : exp T :=
      match e with
      | EXP_Ident id => EXP_Ident (swap id1 id2 id)
      | EXP_Integer _
      | EXP_Float   _
      | EXP_Double  _
      | EXP_Hex     _
      | EXP_Bool    _
      | EXP_Null
      | EXP_Zero_initializer
      | EXP_Cstring _
      | EXP_Undef => e
      | EXP_Struct fields =>
        EXP_Struct (List.map (fun '(t,e) => (swap id1 id2 t, swap_exp id1 id2 e)) fields)
      | EXP_Packed_struct fields =>
        EXP_Packed_struct (List.map (fun '(t,e) => (swap id1 id2 t, swap_exp id1 id2 e)) fields)
      | EXP_Array elts =>
        EXP_Array (List.map (fun '(t,e) => (swap id1 id2 t, swap_exp id1 id2 e)) elts)
      | EXP_Vector elts =>
        EXP_Vector (List.map (fun '(t,e) => (swap id1 id2 t, swap_exp id1 id2 e)) elts)
      | OP_IBinop iop t v1 v2 =>
        OP_IBinop (swap id1 id2 iop) (swap id1 id2 t) (swap_exp id1 id2 v1) (swap_exp id1 id2 v2)
      | OP_ICmp cmp t v1 v2 =>
        OP_ICmp (swap id1 id2 cmp) (swap id1 id2 t) (swap_exp id1 id2 v1) (swap_exp id1 id2 v2)
      | OP_FBinop fop fm t v1 v2 =>
        OP_FBinop (swap id1 id2 fop) fm (swap id1 id2 t) (swap_exp id1 id2 v1) (swap_exp id1 id2 v2)
      | OP_FCmp cmp t v1 v2 =>
        OP_FCmp (swap id1 id2 cmp) (swap id1 id2 t) (swap_exp id1 id2 v1) (swap_exp id1 id2 v2)
      | OP_Conversion conv t_from v t_to =>
        OP_Conversion conv (swap id1 id2 t_from) (swap_exp id1 id2 v) (swap id1 id2 t_to)
      | OP_GetElementPtr t ptrval idxs =>
        OP_GetElementPtr (swap id1 id2 t) (swap id1 id2 (fst ptrval), swap_exp id1 id2 (snd ptrval))
                         (List.map (fun '(a,b) => (swap id1 id2 a, swap_exp id1 id2 b)) idxs)
      | OP_ExtractElement vec idx =>
        OP_ExtractElement (swap id1 id2 (fst vec), swap_exp id1 id2 (snd vec))
                          (swap id1 id2 (fst idx), swap_exp id1 id2 (snd idx))
      | OP_InsertElement  vec elt idx =>
        OP_InsertElement (swap id1 id2 (fst vec), swap_exp id1 id2 (snd vec))
                         (swap id1 id2 (fst elt), swap_exp id1 id2 (snd elt))
                         (swap id1 id2 (fst idx), swap_exp id1 id2 (snd idx))
      | OP_ShuffleVector vec1 vec2 idxmask =>
        OP_ShuffleVector (swap id1 id2 (fst vec1), swap_exp id1 id2 (snd vec1))
                         (swap id1 id2 (fst vec2), swap_exp id1 id2 (snd vec2))
                         (swap id1 id2 (fst idxmask), swap_exp id1 id2 (snd idxmask))
      | OP_ExtractValue  vec idxs =>
        OP_ExtractValue  (swap id1 id2 (fst vec), swap_exp id1 id2 (snd vec))
                         idxs
      | OP_InsertValue vec elt idxs =>
        OP_InsertValue (swap id1 id2 (fst vec), swap_exp id1 id2 (snd vec))
                       (swap id1 id2 (fst elt), swap_exp id1 id2 (snd elt))
                       idxs
      | OP_Select cnd v1 v2 =>
        OP_Select (swap id1 id2 (fst cnd), swap_exp id1 id2 (snd cnd))
                  (swap id1 id2 (fst v1), swap_exp id1 id2 (snd v1))
                  (swap id1 id2 (fst v2), swap_exp id1 id2 (snd v2))
      end.

    Global Instance swap_of_exp : Swap (exp T) := swap_exp.
    Hint Unfold swap_of_exp.

    Definition swap_instr_id (id1 id2:raw_id) (i:instr_id) : instr_id :=
      match i with
      | IId id => IId (swap id1 id2 id)
      | IVoid n => IVoid n  (* TODO: support renaming these too? *)
      end.

    Global Instance swap_of_instr_id : Swap instr_id := swap_instr_id.
    Hint Unfold swap_of_instr_id.

    Definition swap_phi (id1 id2:raw_id) (p:phi T) : phi T :=
      match p with
      | Phi t args => Phi (swap id1 id2 t) (swap id1 id2 args)
      end.
    Global Instance swap_of_phi : Swap (phi T) := swap_phi.
    Hint Unfold swap_of_phi.

    Definition swap_instr (id1 id2:raw_id) (ins:instr T) : instr T :=
      match ins with
      | INSTR_Op op => INSTR_Op (swap id1 id2 op)
      | INSTR_Call fn args => INSTR_Call (swap id1 id2 fn) (swap id1 id2 args)
      | INSTR_Alloca t nb align =>
        INSTR_Alloca (swap id1 id2 t) (swap id1 id2 nb) align
      | INSTR_Load volatile t ptr align =>
        INSTR_Load volatile (swap id1 id2 t) (swap id1 id2 ptr) align
      | INSTR_Store volatile val ptr align =>
        INSTR_Store volatile (swap id1 id2 val) (swap id1 id2 ptr) align
      | INSTR_Comment _
      | INSTR_Fence
      | INSTR_AtomicCmpXchg
      | INSTR_AtomicRMW
      | INSTR_Unreachable
      | INSTR_VAArg
      | INSTR_LandingPad => ins
      end.
    Global Instance swap_of_instr : Swap (instr T) := swap_instr.
    Hint Unfold swap_of_instr.

    Definition swap_terminator (id1 id2:raw_id) (trm:terminator T) : terminator T :=
      match trm with
      | TERM_Ret  v => TERM_Ret (swap id1 id2 v)
      | TERM_Ret_void => TERM_Ret_void
      | TERM_Br v br1 br2 => TERM_Br (swap id1 id2 v) (swap id1 id2 br1) (swap id1 id2 br2)
      | TERM_Br_1 br => TERM_Br_1 (swap id1 id2 br)
      | TERM_Switch  v default_dest brs =>
        TERM_Switch (swap id1 id2 v) (swap id1 id2 default_dest) (swap id1 id2 brs)
      | TERM_IndirectBr v brs =>
        TERM_IndirectBr (swap id1 id2 v) (swap id1 id2 brs)
      | TERM_Resume v => TERM_Resume (swap id1 id2 v)
      | TERM_Invoke fnptrval args to_label unwind_label =>
        TERM_Invoke (swap id1 id2 fnptrval) (swap id1 id2 args) (swap id1 id2 to_label) (swap id1 id2 unwind_label)
      end.
    Global Instance swap_of_terminator : Swap (terminator T) := swap_terminator.
    Hint Unfold swap_of_terminator.

    Global Instance swap_of_param_attr : Swap param_attr :=
      fun id1 id2 l => l.
    Global Instance swap_of_fn_attr : Swap fn_attr :=
      fun id1 id2 l => l.
    Global Instance swap_of_cconv : Swap cconv :=
      fun id1 id2 l => l.
    Global Instance swap_of_linkage : Swap linkage :=
      fun id1 id2 l => l.
    Global Instance swap_of_visibility : Swap visibility :=
      fun id1 id2 l => l.
    Global Instance swap_of_dll_storage : Swap dll_storage :=
      fun id1 id2 l => l.
    Global Instance swap_of_thread_local_storage : Swap thread_local_storage :=
      fun id1 id2 l => l.

    Hint Unfold swap_of_param_attr swap_of_fn_attr swap_of_cconv swap_of_linkage swap_of_visibility swap_of_dll_storage swap_of_thread_local_storage.

    Definition swap_global (id1 id2:raw_id) (g:global T) : (global T) :=
      mk_global
                (swap id1 id2 (g_ident g))
                (swap id1 id2 (g_typ g))
                (swap id1 id2 (g_constant g))
                (swap id1 id2 (g_exp g))
                (swap id1 id2 (g_linkage g))
                (swap id1 id2 (g_visibility g))
                (swap id1 id2 (g_dll_storage g))
                (swap id1 id2 (g_thread_local g))
                (swap id1 id2 (g_unnamed_addr g))
                (swap id1 id2 (g_addrspace g))
                (swap id1 id2 (g_externally_initialized g))
                (swap id1 id2 (g_section g))
                (swap id1 id2 (g_align g)).
    Hint Unfold swap_global.
    Global Instance swap_of_global : Swap (global T) := swap_global.
    Hint Unfold swap_of_global.

    Definition swap_declaration (id1 id2:raw_id) (d:declaration T) : declaration T :=
      mk_declaration
                     (swap id1 id2 (dc_name d))
                     (swap id1 id2 (dc_type d))
                     (swap id1 id2 (dc_param_attrs d))
                     (swap id1 id2 (dc_linkage d))
                     (swap id1 id2 (dc_visibility d))
                     (swap id1 id2 (dc_dll_storage d))
                     (swap id1 id2 (dc_cconv d))
                     (swap id1 id2 (dc_attrs d))
                     (swap id1 id2 (dc_section d))
                     (swap id1 id2 (dc_align d))
                     (swap id1 id2 (dc_gc d)).
    Hint Unfold swap_declaration.
    Global Instance swap_of_declaration : Swap (declaration T) := swap_declaration.
    Hint Unfold swap_of_declaration.

    Definition swap_block (id1 id2:raw_id) (b:block T) : block T :=
      mk_block (swap id1 id2 (blk_id b))
               (swap id1 id2 (blk_phis b))
               (swap id1 id2 (blk_code b))
               (swap id1 id2 (blk_term b))
               (blk_comments b).
    Hint Unfold swap_block.
    Global Instance swap_of_block : Swap (block T) := swap_block.
    Hint Unfold swap_of_block.

    Definition swap_definition {FnBody:Set} `{SF: Swap FnBody} (id1 id2:raw_id) (d:definition T FnBody) : definition T FnBody :=
      mk_definition _
                    (swap id1 id2 (df_prototype d))
                    (swap id1 id2 (df_args d))
                    (swap id1 id2 (df_instrs d)).
    Hint Unfold swap_definition.

    Global Instance swap_of_definition {FnBody:Set} `{SF:Swap FnBody} : Swap (definition T FnBody) :=
      swap_definition.
    Hint Unfold swap_of_definition.

    Fixpoint swap_metadata (id1 id2:raw_id) (m:metadata T) : metadata T :=
      match m with
      | METADATA_Const  tv => METADATA_Const (swap id1 id2 tv)
      | METADATA_Null => METADATA_Null
      | METADATA_Id id => METADATA_Id (swap id1 id2 id)
      | METADATA_String str => METADATA_String (swap id1 id2 str)
      | METADATA_Named strs => METADATA_Named (swap id1 id2 strs)
      | METADATA_Node mds => METADATA_Node (List.map (swap_metadata id1 id2) mds)
      end.
    Global Instance swap_of_metadata : Swap (metadata T) := swap_metadata.
    Hint Unfold swap_of_metadata.

    Definition swap_toplevel_entity {FnBody:Set} `{SF:Swap FnBody} (id1 id2:raw_id) (tle:toplevel_entity T FnBody) :=
      match tle with
      | TLE_Comment msg => tle
      | TLE_Target tgt => TLE_Target (swap id1 id2 tgt)
      | TLE_Datalayout layout => TLE_Datalayout (swap id1 id2 layout)
      | TLE_Declaration decl => TLE_Declaration (swap id1 id2 decl)
      | TLE_Definition defn => TLE_Definition (swap id1 id2 defn)
      | TLE_Type_decl id t => TLE_Type_decl (swap id1 id2 id) (swap id1 id2 t)
      | TLE_Source_filename s => TLE_Source_filename (swap id1 id2 s)
      | TLE_Global g => TLE_Global (swap id1 id2 g)
      | TLE_Metadata id md => TLE_Metadata (swap id1 id2 id) (swap id1 id2 md)
      | TLE_Attribute_group i attrs => TLE_Attribute_group (swap id1 id2 i) (swap id1 id2 attrs)
      end.

    Global Instance swap_of_toplevel_entity {FnBody:Set} `{SF:Swap FnBody} : Swap (toplevel_entity T FnBody) :=
      swap_toplevel_entity.
    Hint Unfold swap_of_toplevel_entity.

    Definition swap_modul {FnBody:Set} `{SF:Swap FnBody} (id1 id2:raw_id) (m:modul T FnBody) : modul T FnBody :=
      mk_modul _
               (swap id1 id2 (m_name m))
               (swap id1 id2 (m_target m))
               (swap id1 id2 (m_datalayout m))
               (swap id1 id2 (m_type_defs m))
               (swap id1 id2 (m_globals m))
               (swap id1 id2 (m_declarations m))
               (swap id1 id2 (m_definitions m)).
    Hint Unfold swap_modul.

    Global Instance swap_of_modul {FnBody:Set} `{SF:Swap FnBody} : Swap (modul T FnBody) :=
      swap_modul.
    Hint Unfold swap_of_modul.

    Definition swap_cfg (id1 id2:raw_id) (CFG:cfg T) : cfg T :=
      mkCFG _ (swap id1 id2 (init _ CFG)) (swap id1 id2 (blks _ CFG)) (swap id1 id2 (args _ CFG)).
    Hint Unfold swap_cfg.

    Global Instance swap_of_cfg : Swap (cfg T) := swap_cfg.
    Hint Unfold swap_of_cfg.

    Global Instance swap_of_mcfg : Swap (mcfg T) := swap.
    Hint Unfold swap_of_mcfg.
  End WithT.

  (******************** Semantic swaps ********************)
  (**
     [GlobalE] and [LocalE] events depend on [raw_id]. The bisimulation between the denotation
     of a MCFG and the one of its swapped version can therefore only be established after
     interpretation of those.
     However we first establish as an intermediate result that the denotation of the swapped
     program, before any interpretation, results in the swapping of original denotation.
   *)

  Instance swap_of_inttyp : forall {x:Z}, Swap (inttyp x) := fun _ id1 id2 a => a.
  Instance swap_of_int1 : Swap int1 := fun id1 id2 a => a.
  Instance swap_of_int32 : Swap int32 := fun id1 id2 a => a.
  Instance swap_of_int64 : Swap int64 := fun id1 id2 a => a.
  Instance swap_of_ll_double : Swap ll_double := fun id1 id2 a => a.
  Instance swap_of_ll_float : Swap ll_float := fun id1 id2 a => a.
  Hint Unfold swap_of_inttyp swap_of_int1 swap_of_int32 swap_of_int64 swap_of_ll_double swap_of_ll_float.

  Instance swap_of_dvalue : Swap dvalue := fun (id1 id2 : raw_id) dv => dv.
  Hint Unfold swap_of_dvalue.

  Instance swap_of_uvalue : Swap uvalue := fun (id1 id2 : raw_id) uv => uv.
  Hint Unfold swap_of_uvalue.

  Program Instance swap_invariant_dvalue_inst : SwapInvariant dvalue := _.
  Next Obligation.
    constructor. intros. unfold swap. reflexivity.
  Defined.

  Program Instance swap_invariant_uvalue_inst : SwapInvariant uvalue := _.
  Next Obligation.
    constructor. intros. unfold swap. reflexivity.
  Defined.

  Instance swap_invariant_of_list {X} `{SwapInvariant X}: SwapInvariant (list X).
  Proof.
    constructor.
    intros ? ? l; induction l as [| x l IH]; [reflexivity | cbn].
    rewrite swap_invariant.
    f_equal; auto.
  Qed.


  Instance swap_of_GlobalE {X} : Swap (LLVMGEnvE X) :=
    fun id1 id2 e =>
      match e with
      | GlobalWrite id v => GlobalWrite (swap id1 id2 id) v
      | GlobalRead id => GlobalRead (swap id1 id2 id)
      end.
  Instance swap_of_LocalE {X} : Swap (LLVMEnvE X) :=
    fun id1 id2 e =>
      match e with
      | LocalWrite id v => LocalWrite (swap id1 id2 id) v
      | LocalRead id => LocalRead (swap id1 id2 id)
      end.
  Instance swap_of_StackE v {X} : Swap (StackE raw_id v X) :=
    fun id1 id2 e =>
      match e with
      | StackPush args => StackPush (List.map (fun '(id,v) => (swap id1 id2 id, v)) args)
      | StackPop => StackPop
      end.
  Instance swap_of_MemoryE {X} : Swap (MemoryE X) := fun id1 id2 x => x.
  Instance swap_of_CallE {X} : Swap (CallE X) := fun id1 id2 x => x.
  Instance swap_of_IntrinsicE {X} : Swap (IntrinsicE X) := fun id1 id2 x => x.
  Instance swap_of_DebugE {X} : Swap (DebugE X) := fun id1 id2 x => x.
  Instance swap_of_FailureE {X} : Swap (FailureE X) := fun id1 id2 x => x.
  Instance swap_of_UndefinedBehaviourE {X} : Swap (UBE X) := fun id1 id2 x => x.
  Instance swap_of_PickE {X} : Swap (PickE X) := fun id1 id2 x => x.
  Hint Unfold swap_of_MemoryE swap_of_StackE swap_of_LocalE swap_of_GlobalE swap_of_CallE swap_of_IntrinsicE swap_of_DebugE FailureE swap_of_FailureE swap_of_UndefinedBehaviourE swap_of_PickE.

  Instance swap_of_sum {A B} `{Swap A} `{Swap B}: Swap (A + B) :=
    fun id1 id2 ab =>
      match ab with
      | inl a => inl (swap id1 id2 a)
      | inr b => inr (swap id1 id2 b)
      end.

  Instance swap_of_sum' {X E F} `{Swap (E X)} `{Swap (F X)}: Swap ((E +' F) X) :=
    fun id1 id2 ef =>
      match ef with
      | inl1 e => inl1 (swap id1 id2 e)
      | inr1 f => inr1 (swap id1 id2 f)
      end.

  Definition swap_itree {X E} `{Swap X} `{forall T, Swap (E T)} (id1 id2:raw_id) (t:itree E X) : itree E X :=
    ITree.map (swap id1 id2) (@translate E E (fun T => swap id1 id2) _ t).
  Instance swap_of_itree {X E} `{SX : Swap X} `{forall T, Swap (E T)}: Swap (itree E X) := swap_itree.
  Hint Unfold swap_of_itree.


  (* Should we swap the arguments? Not when used to create an itree *)
  Instance swap_of_fun {A B} (* `{Swap A} *) `{Swap B}: Swap (A -> B) :=
    fun id1 id2 f a => swap id1 id2 (f a).
  Hint Unfold swap_of_fun.

  (******************** Correctness ********************)

  Section PROOFS.

    Variable id1 id2 : raw_id.

    (******************** Type classes ********************)

    Class Commute_eq1 {A B: Type} `{Swap A} `{Swap B} (f: A -> B) :=
      commute_eq1: forall a, swap id1 id2 (f a) = f (swap id1 id2 a).

    Class Commute_eq_itree1 {E} {A B: Type} `{forall T, Swap (E T)} `{Swap A} `{Swap B} (f: A -> itree E B) :=
      commute_eq_itree1: forall a, swap id1 id2 (f a) ≅ f (swap id1 id2 a).

    Class Commute_eq2 {A B C: Type} `{Swap A} `{Swap B} `{Swap C} (f: A -> B -> C) :=
      commute_eq2: forall a b, swap id1 id2 (f a b) = f (swap id1 id2 a) (swap id1 id2 b).

    Class Commute_eq_itree2 {E} {A B C: Type} `{forall T, Swap (E T)} `{Swap A} `{Swap B} `{Swap C}
          (f: A -> B -> itree E C) :=
      commute_eq_itree2: forall a b, swap id1 id2 (f a b) ≅ f (swap id1 id2 a) (swap id1 id2 b).

    Class Commute_eq_itree3 {E} {A B C D: Type} `{forall T, Swap (E T)} `{Swap A} `{Swap B} `{Swap C} `{Swap D}
          (f: A -> B -> C -> itree E D) :=
      commute_eq_itree3: forall a b c, swap id1 id2 (f a b c) ≅ f (swap id1 id2 a) (swap id1 id2 b) (swap id1 id2 c).

    Class Commute_eq_itree4 {E} {A B C D F: Type} `{forall T, Swap (E T)} `{Swap A} `{Swap B} `{Swap C} `{Swap D} `{Swap F}
          (f: A -> B -> C -> D -> itree E F) :=
      commute_eq_itree4: forall a b c d, swap id1 id2 (f a b c d) ≅ f (swap id1 id2 a) (swap id1 id2 b) (swap id1 id2 c) (swap id1 id2 d).



    (******************** Proofs ********************)

    Lemma swap_subevent {E F} {X} `{Swap X} `{Swap (E X)} `{E -< F} : forall (e:E X),
        (swap id1 id2 (subevent X e)) = subevent X (swap id1 id2 e).
    Proof.
    Abort.

    Lemma swap_trigger_Global
          {X} `{Swap X} {INV: SwapInvariant X}:
      forall (e: LLVMGEnvE X), @ITree.trigger uvalue X (@subevent _ _ _ _ (swap id1 id2 e)) ≅ swap id1 id2 (trigger e).
    Proof.
      intros e.
      unfold trigger.
      unfold swap at 2, swap_of_itree, swap_itree, ITree.map.
      rewrite translate_vis, bind_vis.

      match goal with
      | |- context[subevent ?T ?x] => destruct (subevent T x) eqn:?EQ
      end; [inversion EQ |].
      repeat (
          match goal with
          | s: (?E +' ?F) ?X |- _ => destruct s eqn:?H; [try (inversion EQ; fail) | try (inversion EQ; fail)]; []
          end).
      subst.
      rewrite <- EQ.
      cbn.
      apply eqit_Vis; auto.
      intros ?.
      rewrite translate_ret, bind_ret.
      rewrite swap_invariant; reflexivity.
    Qed.

    Lemma swap_trigger_Local (* {E F: Type -> Type} `{E -< F} `{forall T, Swap (F T)}  `{Swap (E X)} *)
          {X} `{Swap X} {INV: SwapInvariant X}:
      forall (e: LLVMEnvE X), @ITree.trigger uvalue X (@subevent _ _ _ _ (swap id1 id2 e)) ≅ swap id1 id2 (trigger e).
    Proof.
      intros e.
      unfold trigger.
      unfold swap at 2, swap_of_itree, swap_itree, ITree.map.
      rewrite translate_vis, bind_vis.
      match goal with
      | |- context[subevent ?T ?x] => destruct (subevent T x) eqn:?EQ
      end; [inversion EQ |].
      repeat (
          match goal with
          | s: (?E +' ?F) ?X |- _ => destruct s eqn:?H; [try (inversion EQ; fail) | try (inversion EQ; fail)]; []
          end).
      subst.
      rewrite <- EQ.
      cbn.
      apply eqit_Vis; auto.
      intros ?.
      rewrite translate_ret, bind_ret.
      rewrite swap_invariant; reflexivity.
    Qed.

    Lemma swap_trigger_Memory (* {E F: Type -> Type} `{E -< F} `{forall T, Swap (F T)}  `{Swap (E X)} *)
          {X} `{Swap X} {INV: SwapInvariant X}:
      forall (e: MemoryE X), @ITree.trigger uvalue X (@subevent _ _ _ _ (swap id1 id2 e)) ≅ swap id1 id2 (trigger e).
    Proof.
      intros e.
      unfold trigger.
      unfold swap at 2, swap_of_itree, swap_itree, ITree.map.
      rewrite translate_vis, bind_vis.
      match goal with
      | |- context[subevent ?T ?x] => destruct (subevent T x) eqn:?EQ
      end; [inversion EQ |].
      repeat (
          match goal with
          | s: (?E +' ?F) ?X |- _ => destruct s eqn:?H; [try (inversion EQ; fail) | try (inversion EQ; fail)]; []
          end).
      subst.
      rewrite <- EQ.
      cbn.
      apply eqit_Vis; auto.
      intros ?.
      rewrite translate_ret, bind_ret.
      rewrite swap_invariant; reflexivity.
    Qed.
(*
    Instance Commute_lookup_id: Commute_eq_itree1 lookup_id.
    Proof.
      intros i.
      unfold lookup_id.
      destruct i; cbn.
      rewrite <- swap_trigger_Global; reflexivity.
      rewrite <- swap_trigger_Local; reflexivity.
    Qed.

    (* Lemma bind_vis'_ {E F} `{E -< F} {X Y Z} (e: E X) (ek: X -> itree F Y) (k: Y -> itree F Z) : *)
    (*   ITree.bind (vis e ek) k ≅ vis e (fun x => ITree.bind (ek x) k). *)
    (* Admitted. *)

    (* (* Remark: somewhat surprisingly one cannot derive [Swap (E T)> from [Swap (F T)] *) *)
    (* Instance swap_subevent {E F} `{E -< F} `{forall T, Swap (F T)} `{forall T, Swap (E T)} T: *)
    (*   Commute_eq1 (@subevent E F _ T). *)
    (* Proof. *)
    (*   intros e. *)
    (*   unfold subevent. *)

    (* This is really bad: the proof is specific to the ambiant universe of events, [_CFG],
       to the event of concern, [throw], but _also_ to the ReSum instance inferred *)
    Instance Commute_raise {X} `{SX: Swap X} :
      Commute_eq_LLVM1 (@raise _CFG _ _ ).
    Proof.
      intros s; simpl.
      unfold raise.
      unfold swap, swap_of_LLVM, swap_LLVM, Exception.throw, ITree.map.
      rewrite translate_vis, bind_vis.
      match goal with
      | |- context[subevent ?T ?x] => destruct (subevent T x) eqn:?EQ
      end; [inversion EQ |].
      repeat ( match goal with
             | s: (?E +' ?F) ?X |- _ => destruct s eqn:?H; [inversion EQ |]; [] end).
      subst.
      cbn.
      apply eq_itree_Vis; auto; intros [].
    Qed.

    Instance swap_unit: Swap unit := fun _ _ x => x.
    Instance swap_invariant_unit: SwapInvariant unit := {swap_invariant := fun _ _ _ => eq_refl }.

    Instance Commute_debug :
      Commute_eq_LLVM1 (@debug _CFG _).
    Proof.
      intros s; simpl.
      unfold debug.
      unfold swap, swap_of_LLVM, swap_LLVM, ITree.map, trigger.
      rewrite translate_vis, bind_vis.
      match goal with
      | |- context[subevent ?T ?x] => destruct (subevent T x) eqn:?EQ
      end; [inversion EQ |].
      repeat (
          match goal with
          | s: (?E +' ?F) ?X |- _ => destruct s eqn:?H; [try (inversion EQ; fail) | try (inversion EQ; fail)]; []
          end).
      subst.
      cbn.
      apply eq_itree_Vis; auto; intros [].
      rewrite translate_ret, bind_ret; reflexivity.
    Qed.

    Instance Commute_Ret {A} {E: Type -> Type} `{Swap A} `{forall T, Swap (E T)}: @Commute_eq_LLVM1 E A A _ _ _ (fun x => Ret x).
    Proof.
      intros ?.
      unfold swap, swap_of_LLVM, swap_LLVM.
      rewrite translate_ret, map_ret.
      reflexivity.
    Qed.

    (* TODO: turn into an instance *)
    (* Weird to have to assume [SwapInvariant Y]. In particular, is there any case where
       we don't bind with X = Y?
     *)
    Lemma swap_bind {X Y E} `{SX : Swap X} `{SY : Swap Y} `{forall T, Swap (E T)} `{SIY : SwapInvariant Y} :
      forall (e : LLVM E Y) (k : Y -> LLVM E X),
        swap id1 id2 (ITree.bind e k) ≅ ITree.bind (swap id1 id2 e) (fun y => swap id1 id2 (k y)).
    Proof.
      intros.
      unfold swap at 1, swap_of_LLVM, swap_LLVM.
      rewrite translate_bind,map_bind.
      unfold swap at 7.
      rewrite bind_map.
      apply eq_itree_bind; [intros ? | reflexivity].
      rewrite (swap_invariant _ _ a).
      reflexivity.
    Qed.

    (* Annoying form, and impractical to use overall :( *)
    Instance Commute_lift_err {A B} `{SA: Swap A} `{SB: Swap B} f {HC: @Commute_eq_LLVM1 _CFG A B _ _ _ f}:
      Commute_eq_LLVM1 (@lift_err A B _CFG _ f).
    Proof.
      intros []; simpl; rewrite commute_eq_LLVM1; reflexivity.
    Qed.

    Instance Swap_invariant_of_err A `{SwapInvariant A}: SwapInvariant (err A).
    constructor.
    intros ? ? []; [reflexivity |].
    cbn; rewrite swap_invariant; reflexivity.
    Qed.

    Lemma Commute_lift_err' {A B} {SA: Swap A} {SB: Swap B} f {HC: @Commute_eq_LLVM1 _CFG A B _ _ _ f} {SBI: SwapInvariant A}:
      forall c, swap id1 id2 (lift_err f c) ≅ @lift_err A B _CFG _ f c.
    Proof.
      intros ?; rewrite Commute_lift_err, swap_invariant; [reflexivity | typeclasses eauto].
    Qed.

    Lemma Commute_map_monad {E} {X Y} `{Swap X} `{Swap Y} `{forall T, Swap (E T)} {I:SwapInvariant Y}
          (f: X -> LLVM E Y) (l: list X) (IH: forall x, In x l -> swap id1 id2 (f x) ≅ f (swap id1 id2 x)):
      swap id1 id2 (@map_monad (LLVM E) _ X Y f l) ≅ map_monad f (swap id1 id2 l).
    Proof.
      induction l as [| b l IH'].
      - simpl; rewrite Commute_Ret; reflexivity.
      - simpl.
        rewrite swap_bind.
        apply eq_itree_bind; [intros ? |].
        rewrite swap_bind, IH'.
        apply eq_itree_bind; [intros ? | reflexivity].
        rewrite Commute_Ret, swap_invariant; reflexivity.
        intros; apply IH; right; auto.
        rewrite IH; [reflexivity | left; reflexivity].
    Qed.

    Ltac commute_swap :=
      rewrite commute_eq1
      || rewrite Commute_Ret
      || (rewrite Commute_map_monad; try typeclasses eauto)
      || (rewrite Commute_lift_err'; try typeclasses eauto)
      || rewrite <- swap_trigger_Local || rewrite <- swap_trigger_Global || rewrite <- swap_trigger_Memory
      || rewrite commute_eq_LLVM1 || rewrite commute_eq_LLVM2 || rewrite commute_eq_LLVM3.
    Ltac solver := simpl; try commute_swap; reflexivity.

    Ltac step_bind := rewrite swap_bind; apply eq_itree_bind; [intros ? |].

    (* This proof script takes a whole minute to compile *)
    Ltac local_tac := (simpl; try match goal with |- _ ≅ spec_raise _ => solver end).
    Instance Commute_eval_conv_h conv: Commute_eq_LLVM3 (eval_conv_h conv).
    Proof with local_tac.
      intros ? ? ?.
      unfold eval_conv_h.
      Time repeat match goal with
               |- context [match ?x with |_ => _ end] => destruct x; local_tac
                  end;
      solver.
    Qed.

    Instance Commute_eval_conv conv: Commute_eq_LLVM3 (eval_conv conv).
    Proof.
      intros [] b ?; try solver; destruct b; solver.
    Qed.

    Instance Commute_denote_exp : Commute_eq_LLVM2 denote_exp.
    Proof.
      intros top e; revert top.
      induction e; intros top.
      - solver.
      - destruct top as [[]|]; solver.
      - destruct top as [[]|]; solver.
      - destruct top as [[]|]; solver.
      - destruct b; solver.
      - solver.
      - destruct top; solver.
      - solver.
      - destruct top; solver.
      - simpl; step_bind.
        solver.
        rewrite Commute_map_monad; [reflexivity | intros [x t] ?; apply (H (x,t)); auto].
      - destruct top as [[]|]; try solver.
        simpl; step_bind.
        solver.
        rewrite Commute_map_monad; [reflexivity | intros [x t] ?; apply (H (x,t)); auto].
      - simpl; step_bind.
        solver.
        rewrite Commute_map_monad; [reflexivity | intros [x t] ?; apply (H (x,t)); auto].
      - simpl; step_bind.
        solver.
        rewrite Commute_map_monad; [reflexivity | intros [x t] ?; apply (H (x,t)); auto].
      - simpl; repeat step_bind.
        solver.
        rewrite IHe2; solver.
        rewrite IHe1; solver.
      - simpl; repeat step_bind.
        solver.
        rewrite IHe2; solver.
        rewrite IHe1; solver.
      - simpl; repeat step_bind.
        solver.
        rewrite IHe2; solver.
        rewrite IHe1; solver.
      - simpl; repeat step_bind.
        solver.
        rewrite IHe2; solver.
        rewrite IHe1; solver.
      - simpl; repeat step_bind.
        solver.
        rewrite IHe; solver.
      - destruct ptrval; simpl; repeat step_bind.
        solver.
        rewrite Commute_map_monad; [reflexivity | intros [x t'] ?; apply (H (x,t')); auto].
        rewrite IHe; solver.
      - solver.
      - solver.
      - solver.
      - destruct vec; simpl; repeat step_bind.
        solver.
        rewrite IHe; solver.
      - solver.
      - destruct cnd,v1,v2; simpl; repeat step_bind.
        solver.
        rewrite IHe1; solver.
        rewrite IHe0; solver.
        rewrite IHe; solver.
    Qed.

    Instance Commute_eval_op: Commute_eq_LLVM1 eval_op.
    Proof.
      intros ?; unfold eval_op; solver.
    Qed.

    Instance Commute_denote_instr: Commute_eq_LLVM1 denote_instr.
    Proof.
      intros [[] []]; try solver.
      - simpl; step_bind; solver.
      - destruct fn; simpl; repeat step_bind; try solver.
        + admit. (* Intrinsics *)
        + rewrite Commute_map_monad.
          solver.
          intros [] ?; solver.
      - simpl; step_bind; solver.
      - destruct ptr; simpl; repeat step_bind; try solver.
      - destruct fn; simpl; repeat step_bind; try solver.
        + admit. (* Intrinsics *)
        + rewrite Commute_map_monad.
          solver.
          intros [] ?; solver.
      - destruct val, ptr; simpl; repeat step_bind; try solver.
    Admitted.

    Instance Commute_denote_terminator: Commute_eq_LLVM1 denote_terminator.
    Proof.
      intros []; try solver.
      - destruct v; simpl.
        rewrite swap_bind; apply eq_itree_bind; [intros ? | ].
        solver.
        cbn; rewrite Commute_denote_exp; reflexivity.
      - destruct v; simpl.
        rewrite swap_bind; apply eq_itree_bind; [intros ? | ].
        destruct a; try solver.
        match goal with | |- context[if ?e then _ else _] => destruct e; solver end.
        cbn; rewrite Commute_denote_exp; reflexivity.
    Qed.

    Instance Commute_denote_code: Commute_eq_LLVM1 denote_code.
    intros c; induction c as [| i c IH]; [solver |].
    simpl; rewrite swap_bind; apply eq_itree_bind; [intros ?; apply IH | solver].
    Qed.

    Instance Commute_denote_block: Commute_eq_LLVM1 denote_block.
    Proof.
      intros []; cbn.
      rewrite swap_bind; apply eq_itree_bind; [intros ? |].
      destruct blk_term; solver.
      solver.
    Qed.

    Lemma swap_raw_id_inj : forall (k j:raw_id), swap id1 id2 k = swap id1 id2 j -> k = j.
    Proof.
      intros.
      unfold_swaps. unfold swap_raw_id in *.
      simpl_ifs; unfold eqv, eqv_raw_id in *; subst; try reflexivity; try contradiction.
    Qed.

   Lemma swap_eq_dec_raw_id_left: forall (x y: raw_id) Pf,
        RawIDOrd.eq_dec x y = left Pf ->
        exists Pf', RawIDOrd.eq_dec (swap id1 id2 x) (swap id1 id2 y) = left Pf'.
   Proof.
     intros; subst.
     exists eq_refl.
     destruct (RawIDOrd.eq_dec (swap id1 id2 y) (swap id1 id2 y)).
     f_equal; apply Eqdep_dec.UIP_dec; apply RawIDOrd.eq_dec.
     contradiction n; reflexivity.
   Qed.

   Lemma swap_eq_dec_raw_id_left': forall (x y: raw_id) Pf,
       RawIDOrd.eq_dec (swap id1 id2 x) (swap id1 id2 y) = left Pf ->
       exists Pf', RawIDOrd.eq_dec x y = left Pf'.
   Proof.
     intros; subst.
     generalize (swap_raw_id_inj _ _ Pf); intros ->.
     exists eq_refl.
     destruct (RawIDOrd.eq_dec y y).
     f_equal; apply Eqdep_dec.UIP_dec; apply RawIDOrd.eq_dec.
     contradiction n; reflexivity.
   Qed.

   Lemma swap_eq_dec_raw_id_right: forall (x y: raw_id) Pf,
        RawIDOrd.eq_dec x y = right Pf ->
        exists Pf', RawIDOrd.eq_dec (swap id1 id2 x) (swap id1 id2 y) = right Pf'.
   Proof.
     intros; subst.
     destruct (RawIDOrd.eq_dec (swap id1 id2 x) (swap id1 id2 y)) eqn:Pf'.
     - apply swap_eq_dec_raw_id_left' in Pf'; destruct Pf' as [Pf' EQ]; rewrite EQ in H; inversion H.
     - exists n; reflexivity.
   Qed.

   Lemma swap_assoc_raw_id {Y} `{Swap Y} (x: raw_id) (l: list (raw_id * Y)):
     swap id1 id2 (assoc RawIDOrd.eq_dec x l) = assoc RawIDOrd.eq_dec (swap id1 id2 x) (swap id1 id2 l).
   Proof.
     induction l as [| [id y] l IH]; simpl; auto.
     match goal with | |- context[if ?e then _ else _] => destruct e eqn:EQ end; subst.
     - apply swap_eq_dec_raw_id_left in EQ; destruct EQ as [Pf EQ].
       rewrite EQ; reflexivity.
     - apply swap_eq_dec_raw_id_right in EQ; destruct EQ as [Pf EQ].
       rewrite EQ, IH; reflexivity.
   Qed.

   Instance Commute_denote_phi: Commute_eq_LLVM2 denote_phi.
    Proof.
      intros ? (? & ? & ?).
      generalize (swap_assoc_raw_id a args); intros EQ.
      unfold denote_phi.
      match goal with |- context[raise ?s] => set (s1 := s) end.
      match goal with |- context[raise (?s ++ ?x)] => set (s2 := s ++ x) end.
      simpl.
      unfold block_id in *.
      match goal with
      | |-  _ ≅ match ?x with |_ => _ end => destruct x
      end.
      - match type of EQ with
        | swap _ _ ?x = _ => destruct x eqn:EQ'
        end; inv EQ.
        rewrite swap_bind; apply eq_itree_bind; [intros ?; solver | solver].
      - match type of EQ with
        | swap _ _ ?x = _ => destruct x eqn:EQ'
        end; inv EQ.
        rewrite Commute_raise.
        (* Two strings here are actually different due to error messages containing the ids *)
        admit.
    Admitted.

   Instance Commute_denote_cfg: Commute_eq_LLVM1 denote_cfg.
   Proof.
     intros ?.
     unfold denote_cfg.
   Admitted.

   Instance Commute_denote_mcfg: Commute_eq_LLVM4 denote_mcfg.
   Proof.
     intros ? ? ? ?.
     unfold denote_mcfg.
   Admitted.
*)

  End PROOFS.
End RENAMING.

(* Scrap *)
(*
    (*
  (* TODO: Add to Coq Library *)
  Lemma Empty_Equals : forall {X} (e:ENV.t X), ENV.Empty e -> ENV.Equal (ENV.empty X) e.
  Proof.
    intros.
    apply ENVFacts.Equal_mapsto_iff.
    intros k x.
    pose (H1 := H k x). clearbody H1.
    split.
    intros H2.
    apply ENVFacts.empty_mapsto_iff in H2. contradiction.
    intros. contradiction.
  Qed.

  (* TODO: Add to Coq Library *)
  Lemma find_Empty_none : forall {X} (e:ENV.t X) (id:raw_id), ENV.Empty e -> ENV.find id e = None.
  Proof.
    intros.
    apply ENVFacts.not_find_in_iff.
    unfold not. intros H1.
    apply (@ENVFacts.empty_in_iff X id).
    apply Empty_Equals in H.
    rewrite H. assumption.
  Qed.
     *)
  (*
(* Parameter fold : forall A: Type, (key -> elt -> A -> A) -> t elt -> A -> A. *)
Definition swap_ENV {X} `{SX : Swap X} (id1 id2:raw_id) (m:ENV.t X) : ENV.t X :=
  ENV.fold (fun k v n => ENV.add (swap id1 id2 k) (swap id1 id2 v) n) m (ENV.empty X).
Hint Unfold swap_ENV.
  *)


(*
  Lemma swap_ENV_find : forall {X} `{SX : Swap X} (e:ENV.t X) (id:raw_id),
      (ENV.find (swap id1 id2 id) (swap id1 id2 e)) = swap id1 id2 (ENV.find id e).
  Proof.
    intros X SX.
    unfold_swaps.
    intros e id.
    apply ENVProps.fold_rec.
    - intros m H.
      rewrite find_Empty_none. rewrite find_Empty_none. reflexivity. assumption.
      apply ENV.empty_1.

    - intros k e0 a m' m'' H H0 H1 H2.
      rewrite H1.
      repeat rewrite ENVFacts.add_o.
      destruct (ENVProps.F.eq_dec k id).
      subst.
      (* Set Printing All. (* The ENV.key vs. raw_id types in swap make destruction with the displayed syntax not work. *) *)
      destruct (RawIDOrd.eq_dec (swap_raw_id id1 id2 id) (swap_raw_id id1 id2 id)).
      (* Unset Printing All. *)
      simpl. reflexivity. contradiction.

      destruct (RawIDOrd.eq_dec (swap_raw_id id1 id2 k) (swap_raw_id id1 id2 id)).
      apply swap_raw_id_inj in e1. contradiction.
      apply H2.
  Qed.
   *)
  (*
  Lemma swap_lookup_env : forall {X} `{SX : Swap X} (e:ENV.t X) (id:raw_id),
      (lookup_env (swap id1 id2 e) (swap id1 id2 id) = swap id1 id2 (lookup_env e id)).
  Proof.
    intros.
    unfold lookup_env.
    rewrite swap_ENV_find.
    (* FIXME: error message doesn't work *)
    (* destruct (ENV.find id e); unfold_swaps; simpl; reflexivity. *)
  Admitted.


  Lemma swap_eval_i1_op : forall (iop:ibinop) (x y:inttyp 1),
      eval_int_op (swap id1 id2 iop) (swap id1 id2 x) (swap id1 id2 y) = swap id1 id2 (eval_int_op iop x y).
  Proof.
    unfold_swaps.
    intros iop x y.
    reflexivity.
  Qed.

  Lemma swap_eval_i32_op : forall (iop:ibinop) (x y:inttyp 32),
      eval_int_op (swap id1 id2 iop) (swap id1 id2 x) (swap id1 id2 y) = swap id1 id2 (eval_int_op iop x y).
  Proof.
    unfold_swaps.
    intros iop x y.
    reflexivity.
  Qed.

  Lemma swap_eval_i64_op : forall (iop:ibinop) (x y:inttyp 64),
      eval_int_op (swap id1 id2 iop) (swap id1 id2 x) (swap id1 id2 y) = swap id1 id2 (eval_int_op iop x y).
  Proof.
    unfold_swaps.
    intros iop x y.
    reflexivity.
  Qed.

  Lemma swap_integer_op : forall (bits:Z) (iop:ibinop) (x y:inttyp bits),
   integer_op bits (swap id1 id2 iop) (swap id1 id2 x) (swap id1 id2 y) = swap id1 id2 (integer_op bits iop x y).
  Proof.
    intros bits iop x y.
    unfold_swaps.
    destruct (integer_op bits iop x y); reflexivity.
  Qed.


  Lemma swap_eval_iop : forall iop v1 v2,
      eval_iop (swap id1 id2 iop) (swap id1 id2 v1) (swap id1 id2 v2) =
      swap id1 id2 (eval_iop iop v1 v2).
  Proof.
    intros iop v1 v2.
    unfold_swaps.
    destruct (eval_iop iop v1 v2); reflexivity.
  Qed.

  Lemma swap_eval_icmp : forall icmp v1 v2,
      eval_icmp (swap id1 id2 icmp) (swap id1 id2 v1) (swap id1 id2 v2) =
      swap id1 id2 (eval_icmp icmp v1 v2).
  Proof.
    intros icmp v1 v2.
    unfold_swaps.
    destruct (eval_icmp icmp v1 v2); reflexivity.
  Qed.
   *)
  (*
  (* Before changing ITrees to records, we could prove _equality_ here.  Now we prove
     only bisimulation?
   *)
  Lemma swap_raise {X} `{SX: Swap X} : forall s : string, (@raise string Trace _ _ s) ≅ (swap id1 id2 (@raise string Trace _ _ s)).
  Proof.
    intros s.
    econstructor.
    econstructor.
  Qed.


  Lemma swap_ret {X E} `{SX: Swap X} : forall x, (Ret (swap id1 id2 x) : itree E (_+X)) ≅ swap id1 id2 (Ret x).
  Proof.
    intros x.
    econstructor.
    econstructor.
  Qed.


    Ltac bisim :=
    repeat (cbn; match goal with
                 | [H : _ |- go ?X ≅ swap ?ID1 ?ID2 (go ?Y) ] => econstructor
                 | [H : _ |- ?X ≅ swap ?ID1 ?ID2 ?X ] => econstructor; cbn
                 | [ _ : _ |- match swap ?ID1 ?ID2 ?X with _ => _ end ≅ swap ?ID1 ?ID2 (match ?X with _ => _  end) ] => destruct X; cbn
                 | [ _ : _ |- eq_itreeF eq_itree ?X ?X ] => econstructor; cbn
                 | [ _ : _ |- eq_itreeF eq_itree (RetF ?X) (RetF ?Y) ] => econstructor; cbn
                 | [ _ : _ |- eq_itreeF eq_itree (TauF ?X) (TauF ?Y) ] => econstructor; cbn
                 | [ _ : _ |- eq_itreeF eq_itree (VisF _ ?X ?K) (VisF _ ?Y ?K2) ] => econstructor; cbn
                 | [ _ : _ |- (lift_err (swap ?ID1 ?ID2 ?E) ?k) ≅ swap ?ID1 ?ID2 (lift_err ?E ?k) ] => destruct E; cbn
                end).


  Lemma swap_lift_err {X:Type} `{SX: Swap X} :
      forall a, (fun x : err X => Ret (swap id1 id2 x)) a ≅ (lift_err (fun x : X => swap id1 id2 (ret x))) a.
  Proof.
    intros a.
    destruct a; cbn.
    - reflexivity.
    - constructor. econstructor.
  Qed.


  Lemma swap_bind {X Y} `{SX : Swap X} `{SY : Swap Y} `{SIY : SwapInvariant Y} :
    forall (e : Trace Y) (k : Y -> Trace X),
      swap id1 id2 (bind e k) ≅ bind (swap id1 id2 e) (fun y => swap id1 id2 (k y)).
  Proof.
    cofix ch.
    intros e k.
    econstructor.
    cbn.
    destruct (observe e).
    - cbn. destruct r; cbn.
      + econstructor.
      + rewrite swap_invariant.
        destruct (observe (k y)) eqn:Heq; cbn; econstructor.
        * reflexivity.
        * intros. reflexivity.
    - econstructor.
      pose bind_associativity as HA.
      unfold bind, monad_trace, bind_trace, ITree.bind in HA.








  Admitted.





  Lemma swap_eval_exp : forall CFG g e top o,
      eval_exp (swap id1 id2 CFG) (swap id1 id2 g) (swap id1 id2 e) (swap id1 id2 top) (swap id1 id2 o) ≅
      swap id1 id2 (eval_exp CFG g e top o).
  Proof.
    intros CFG g e top.
    unfold err in *.
    induction o; bisim.
    - cbn. rewrite swap_lookup_id.
      bisim.
(*
    - destruct (coerce_integer_to_int sz x); bisim.

    - destruct b; bisim.

    - destruct top. simpl.
      induction fields; simpl.
      + bisim.
      + destruct a. cbn. bisim.


    - cbn. econstructor. econstructor.

    - cbn. destruct top; try destruct d; simpl; try (econstructor; econstructor).

    - cbn. econstructor.

   *)
(* Change to the ITree affected the way that errors need to be handled here. *)

  Admitted.



  Lemma swap_step : forall (CFG:mcfg) (s:state),
      eq_itree (step (swap id1 id2 CFG) (swap id1 id2 s)) (swap id1 id2 (step CFG s)).
  Proof.
    intros CFG.
    destruct s as [[[g pc] e] k].
    unfold_swaps. simpl.
  Admitted.


  Lemma swap_step_sem : forall (CFG:mcfg) (r:result),
      eq_itree (step_sem (swap id1 id2 CFG) (swap id1 id2 r)) (swap id1 id2 (step_sem CFG r)).
  Proof.
    intros CFG r.
    (*
    cofix swap_step_sem.
    destruct r.
    - rewrite Trace.matchM. simpl.
      assert (swap id1 id2 (step_sem CFG (Done v)) = Trace.idM (swap id1 id2 (step_sem CFG (Done v)))).
      rewrite Trace.matchM at 1. reflexivity.
      rewrite H. simpl. constructor.


    - unfold swap at 2. simpl.
      rewrite Trace.matchM. simpl.
   *)

  Admitted.

   *)
*)
*)
