Require Import Arith List Util.

Import ListNotations.


Module Type EFF_SYN.

  Parameters op hnd hty : Set.

End EFF_SYN.


Module Eff_Base (Import ESP:EFF_SYN).

  Inductive sym : Set := Sym :> nat -> sym.

  Inductive ty : Set := H : hty -> ty | F1 | Bot.

  Definition sig := list ty.

  Inductive exp : Set :=
  | Nil : exp
  | Seq : exp -> exp -> exp
  | Op : sym -> op -> exp
  | With : (hnd * list exp) -> exp -> exp.

  Module Type EFF_PARAM.

    Parameter react : hnd * list exp -> op -> exp -> exp -> Prop.

    Parameter wt_op_aux : op -> ty -> Prop.

    Parameter wt_hnd_aux : hnd -> list ty -> ty -> Prop.

    (* A handler that takes program syntax as parameters could 'react'
       to produce a term that adds or removes handlers. Wt_hnd_sym
       takes determines the handler environment (sig) for each handler argument
       based on the handler environment of the With expression.
       Examples: - recursive vs. non-recursive handlers
                 - a function should be invoked in an environment with a 
                   'return' continuation bound
     *)
    Parameter wt_hnd_sym : hnd -> ty -> sig -> list sig -> Prop.

  End EFF_PARAM.


  Module Eff_Semantics (Import ETP:EFF_PARAM).

    Infix "#" := (Op) (at level 1).
    Infix ";;" := (Seq) (at level 70, right associativity).

    Inductive step : exp -> exp -> Prop :=
    | step_nil : 
      step Nil Nil
    | step_hoist : forall s h o k,
      step (With h ((S s)#o ;; k)) (s#o ;; With h k)
    | step_eff : forall h o e k,
      react h o k e -> step (With h (O#o ;; k)) e
    | step_with : forall h e e',
      step e e' ->
      step (With h e) (With h e').

    Inductive reduce : exp -> exp -> Prop :=
    | reduce_refl : forall e, reduce e e
    | reduce_trans : forall e1 e2 e3, step e1 e2 -> reduce e2 e3 -> reduce e1 e3.

    Inductive wt_exp (E:sig) : exp -> ty -> Prop :=
    | wt_nil :
      wt_exp E Nil Bot
    | wt_seq : forall e1 e2, 
      wt_exp E e1 F1 -> 
      wt_exp E e2 Bot -> 
      wt_exp E (e1 ;; e2) Bot
    | wt_op : forall s o th,
      nth_error E s = Some th ->
      wt_op_aux o th ->
      wt_exp E s#o F1
    | wt_with : forall Es es ts h th e,
      wt_hnd_aux h ts th ->
      wt_hnd_sym h th E Es ->
      Forall3 wt_exp Es es ts ->
      wt_exp (th::E) e Bot ->
      wt_exp E (With (h, es) e) Bot.

    Module Type EFF_SAFETY_PARAM.

      Axiom react_preservation : forall E Es o h ts th k es e,
        wt_hnd_aux h ts th ->
        wt_hnd_sym h th E Es ->
        Forall3 wt_exp Es es ts ->
        wt_exp (th::E) k Bot ->
        wt_op_aux o th ->
        react (h, es) o k e ->
        wt_exp E e Bot.
     
      Axiom react_progress : forall E Es o h th es ts k,
        wt_hnd_aux h ts th ->
        wt_hnd_sym h th E Es ->
        Forall3 wt_exp Es es ts ->
        wt_op_aux o th ->
        exists e, react (h, es) o k e.

    End EFF_SAFETY_PARAM.

    Module Eff_Safety (Import SP:EFF_SAFETY_PARAM).

      Inductive nf : exp -> Prop :=
      | nf_intro : forall s o k,
        nf (s#o ;; k).
  
      Lemma step_preservation : forall E e e' t,
        step e e' ->
        wt_exp E e t ->
        wt_exp E e' t.
      Proof.
        intros until 1. generalize dependent E. generalize dependent t.
        induction H0; subst.
  
        (* step_nil *) auto.
        (* step_hoist *) inversion 1; subst. inversion H7; subst.
          inversion H6; subst. simpl in *.
          econstructor. econstructor; eauto. econstructor; eauto.
        (* step_eff *) inversion 1; subst. inversion H8; subst.
          inversion H7; subst. simpl in *. inversion H10. subst th; clear H10.
          eapply react_preservation; eauto.
        (* step_with *) inversion 1; subst. 
          inversion H1; subst.
          econstructor; eauto.
      Qed.

      Lemma step_progress : forall E e,
        wt_exp E e Bot ->
        nf e \/ exists e', step e e'.
      Proof.
        intros until 1.
        remember Bot as t.
        induction H0; subst.

        right. eexists; constructor.

        left. inversion H0_; subst. constructor.
        
        inversion Heqt. specialize (IHwt_exp eq_refl). inversion_clear IHwt_exp.
        right. inversion H4; subst.
          destruct s as [[|]].
            inversion H3; subst. inversion H7; subst.
              simpl in H9. inversion H9; subst th.
              ecase react_progress; eauto. intros; eexists. eapply step_eff; eauto. 
            eexists. econstructor.

        right. destruct H4 as [? ?]. eexists. econstructor; eauto.
      Qed.

    End Eff_Safety.

  End Eff_Semantics.

End Eff_Base.
  

Module Counter.

  Module Import Syn <: EFF_SYN.
    Inductive op' : Set := Incr.
  
    Inductive hnd' : Set := Counter : nat -> hnd'.
  
    Inductive hty' : Set := Cty.

    Definition op := op'.
    Definition hnd := hnd'.
    Definition hty := hty'.
  End Syn.
  
  Module Import Base := Eff_Base Syn.
  
  Module Import Param <: EFF_PARAM.
    Inductive wt_op_aux' : op -> ty -> Prop :=
    | wt_op_aux_incr : wt_op_aux' Incr (H Cty).

    Inductive wt_hnd_aux' : hnd -> list ty -> ty -> Prop :=
    | wt_hnd_aux_counter : forall n, wt_hnd_aux' (Counter n) [] (H Cty).

    Inductive wt_hnd_sym' : hnd -> ty -> sig -> list sig -> Prop :=
    | wt_hnd_sym_counter : forall E n, wt_hnd_sym' (Counter n) (H Cty) E [].

    Inductive react' : hnd * list exp -> op -> exp -> exp -> Prop :=
    | react_incr : forall n k, react' (Counter n, []) Incr k
                                      (With (Counter (S n), []) k).

    Definition wt_op_aux := wt_op_aux'.
    Definition wt_hnd_aux := wt_hnd_aux'.
    Definition wt_hnd_sym := wt_hnd_sym'.
    Definition react := react'.
  End Param.

  Module Import Semantics := Eff_Semantics(Param).
  
  Example prog0 : exp := With (Counter 0, []) (
                              Op 0 Incr ;;
                              Op 0 Incr ;;
                              Nil
                              ).

  Goal wt_exp [] prog0 Bot.
  Proof. repeat (econstructor; eauto). Qed.

  Goal reduce prog0 (With (Counter 2, []) Nil).
  Proof. repeat (econstructor; eauto). Qed.

  Example prog1 : exp := With (Counter 0, []) (
                         With (Counter 1, []) (
                                Op 0 Incr ;;
                                Op 1 Incr ;;
                                Nil
                              )).
                         
  Goal wt_exp [] prog1 Bot.
  Proof. repeat (econstructor; eauto). Qed.

  Module Safety_Param <: EFF_SAFETY_PARAM.

    Lemma react_preservation : forall E Es o h ts th k es e,
      wt_hnd_aux h ts th ->
      wt_hnd_sym h th E Es ->
      Forall3 wt_exp Es es ts ->
      wt_exp (th::E) k Bot ->
      wt_op_aux o th ->
      react (h, es) o k e ->
      wt_exp E e Bot.
    Proof.
      intros.
      inversion H5; subst.     
      econstructor. 
        inversion H1; subst. econstructor.
        inversion H1; subst. econstructor.
        inversion H2; subst. econstructor.
        inversion H0; subst. assumption.
    Qed.
      
    Lemma react_progress : forall E Es o h th es ts k,
      wt_hnd_aux h ts th ->
      wt_hnd_sym h th E Es ->
      Forall3 wt_exp Es es ts ->
      wt_op_aux o th ->
      exists e, react (h, es) o k e.
    Proof.
      intros. inversion H0; subst.
      inversion H1; inversion H2; inversion H3; subst.
      eexists. econstructor.
    Qed.

  End Safety_Param.

  Module Import Safety := Eff_Safety (Safety_Param).

End Counter.


Module SimpleLang.

  Module Import Syn <: EFF_SYN.

    Inductive op' : Set := Incr | J : nat -> op'.
  
    Inductive hnd' : Set := Rec : nat -> hnd'.
  
    Inductive hty' : Set := Tbl : nat -> hty'. (* jump table *)

    Definition op := op'.
    Definition hnd := hnd'.
    Definition hty := hty'.
  End Syn.
  
  Module Import Base := Eff_Base Syn.
  
  Module Import Param <: EFF_PARAM.
    Inductive wt_op_aux' : op -> ty -> Prop :=
    | wt_op_aux_incr : forall n, wt_op_aux' Incr (H (Tbl n))
    | wt_op_aux_j : forall m n, m < n -> wt_op_aux' (J m) (H (Tbl n)).

    Inductive wt_hnd_aux' : hnd -> list ty -> ty -> Prop :=
    | wt_hnd_aux_counter : forall m n, wt_hnd_aux' (Rec n) (replicate Bot m) (H (Tbl m)).

    Inductive wt_hnd_sym' : hnd -> ty -> sig -> list sig -> Prop :=
    | wt_hnd_sym_counter : forall E m n, wt_hnd_sym' (Rec n) (H (Tbl m)) E (replicate (H (Tbl m)::E) m).

    Inductive react' : hnd * list exp -> op -> exp -> exp -> Prop :=
    | react_incr : forall n k a, react' (Rec n, a) Incr k
                                        (With (Rec (S n), a) k)
    | react_j : forall n m k a, react' (Rec m, a) (J n) k
                                       (With (Rec m, a) (nth n a Nil)).

    Definition wt_op_aux := wt_op_aux'.
    Definition wt_hnd_aux := wt_hnd_aux'.
    Definition wt_hnd_sym := wt_hnd_sym'.
    Definition react := react'.
  End Param.

  Module Import Semantics := Eff_Semantics(Param).
  
  Example prog0 : exp := With (Rec 0, []) (
                              Op 0 Incr ;;
                              Op 0 Incr ;;
                              Nil
                              ).

  Goal wt_exp [] prog0 Bot.
  Proof. repeat (econstructor; eauto). instantiate (1:=0); simpl; constructor. Qed.
         

  Goal reduce prog0 (With (Rec 2, []) Nil).
  Proof. repeat (econstructor; eauto). Qed.

  Example prog1 : exp := With (Rec 0, [0 # Incr ;; 0 # Incr ;; 0 # (J 0) ;; Nil]) (
                                0 # (J 0) ;; 
                                Nil
                              ).
                         
  Goal wt_exp [] prog1 Bot.
  Proof. repeat (econstructor; eauto). 
         simpl. repeat (econstructor; eauto). 
  Qed.

  Ltac ss := eapply reduce_trans; [repeat econstructor|].

  Goal exists e, reduce prog1 e.
    eexists. unfold prog1.
    ss. ss. ss. ss. ss. ss. ss. ss. ss. ss. ss. 
    ss. ss. ss. ss. ss. ss. ss. ss. ss. ss. ss. 
    apply reduce_refl.
  Qed.    
    
  Module Safety_Param <: EFF_SAFETY_PARAM.

    Lemma react_preservation : forall E Es o h ts th k es e,
      wt_hnd_aux h ts th ->
      wt_hnd_sym h th E Es ->
      Forall3 wt_exp Es es ts ->
      wt_exp (th::E) k Bot ->
      wt_op_aux o th ->
      react (h, es) o k e ->
      wt_exp E e Bot.
    Proof.
      intros.
      inversion H5; subst.
        inversion H0; inversion H1; subst. inversion H9; subst m0.
          econstructor. econstructor. econstructor. eassumption. eassumption.

        inversion H0; inversion H1; subst. inversion H9; subst m0.
          econstructor. econstructor. econstructor. eassumption.

          (* ugh... *)
          clear - H2. 
          set (m2:=m1). assert (m1 = m2) as Heq by reflexivity. rewrite Heq in H2 at 1.
          clearbody m2. clear Heq.
          remember (replicate (_::_) _) as l.
          remember (replicate Bot _) as l'.
          generalize dependent m1.
          generalize dependent n.

          induction H2. destruct n; simpl; econstructor; eauto.
          intros. 
          destruct m1; simpl in *. inversion Heql.
          destruct n0; inversion Heql; inversion Heql'; subst.
            assumption.
            eapply IHForall3; eauto. 
    Qed.
      
    Lemma react_progress : forall E Es o h th es ts k,
      wt_hnd_aux h ts th ->
      wt_hnd_sym h th E Es ->
      Forall3 wt_exp Es es ts ->
      wt_op_aux o th ->
      exists e, react (h, es) o k e.
    Proof.
      intros. inversion H0; subst.
      inversion H3; subst.
      eexists. econstructor.
      eexists. econstructor.
    Qed.

  End Safety_Param.

  Module Import Safety := Eff_Safety (Safety_Param).

End SimpleLang.


(* For even slightly more realistic languages "programming by effect" forces us 
   to use a single top-level handler. This shouldn't be the case when we add 
   values and binding to the language. *)

Module Assembly.

  Module Import Syn <: EFF_SYN.

    Inductive loc : Set := Loc : nat -> loc.
    Scheme Equality for loc.

    Notation "$ x" := (Loc x) (at level 1, format "$ x").

    Inductive ari : Set := Plus | Minus | Times | Eq | Le | And | Or.

    Inductive op' : Set := 
    | Bop : loc -> ari -> loc -> loc -> op'  
    | Mov : loc -> nat -> op'
    | J : nat -> op'
    | Jz : loc -> nat -> op'
    | Ret : loc -> op'
    | Halt : nat -> op'.
  
    Inductive hnd' : Set := Config : (loc -> nat) -> hnd'.
  
    Inductive hty' : Set := Cfg : nat -> hty' | Exit. (* again, size of jump table *)

    Definition op := op'.
    Definition hnd := hnd'.
    Definition hty := hty'.
  End Syn.
  
  Module Import Base := Eff_Base Syn.
  
  Module Import Param <: EFF_PARAM.
    Inductive wt_op_aux' : op -> ty -> Prop :=
    | wt_op_aux_bop : forall n d a s1 s2, wt_op_aux' (Bop d a s1 s2) (H (Cfg n))
    | wt_op_aux_mov : forall n d m, wt_op_aux' (Mov d m) (H (Cfg n))
    | wt_op_aux_j : forall m n, m < n -> wt_op_aux' (J m) (H (Cfg n))
    | wt_op_aux_jz : forall m n s, m < n -> wt_op_aux' (Jz s m) (H (Cfg n))
    | wt_op_aux_ret : forall n s, wt_op_aux' (Ret s) (H (Cfg n))
    | wt_op_aux_halt : forall n, wt_op_aux' (Halt n) (H Exit).

    (* note: there is no handler for halt (of type Exit) *)
    Inductive wt_hnd_aux' : hnd -> list ty -> ty -> Prop :=
    | wt_hnd_aux_counter : forall m f, wt_hnd_aux' (Config f) (replicate Bot m) (H (Cfg m)).

    (* note: can only have one top-level handler! *)
    Inductive wt_hnd_sym' : hnd -> ty -> sig -> list sig -> Prop :=
    | wt_hnd_sym_counter : forall m f, wt_hnd_sym' (Config f) (H (Cfg m)) [H Exit] (replicate ([H (Cfg m)]) m).

    Definition ari_denote (a:ari) : nat -> nat -> nat :=
       match a with
         | Plus => plus
         | Minus => minus
         | Times => mult
         | Eq => fun m n => if beq_nat m n then 1 else 0
         | Le => fun m n => if leb m n then 1 else 0
         | And => fun m n => if orb (beq_nat m 0) (beq_nat n 0) then 0 else 1
         | Or => fun m n => if andb (beq_nat m 0) (beq_nat n 0) then 0 else 1
       end.
               
    Inductive react' : hnd * list exp -> op -> exp -> exp -> Prop :=
    | react_bop : forall f k ks a d s1 s2, 
                    let f' l := if loc_eq_dec l d 
                                then ari_denote a (f s1) (f s2)
                                else f l in
                    react' (Config f, ks) (Bop d a s1 s2) k
                           (With (Config f', ks) k)
    | react_mov : forall f k ks d m,
                    let f' l := if loc_eq_dec l d 
                                then m 
                                else f l in
                    react' (Config f, ks) (Mov d m) k
                           (With (Config f', ks) k)
    | react_j : forall n f k ks, 
                  react' (Config f, ks) (J n) k
                         (With (Config f, ks) (nth n ks Nil))
    | react_jz : forall n f k ks s, 
                   react' (Config f, ks) (Jz s n) k
                          (if (beq_nat (f s) 0) 
                           then (With (Config f, ks) (nth n ks Nil))
                           else (With (Config f, ks) k))
    | react_ret : forall f k ks s,
                    react' (Config f, ks) (Ret s) k
                           (Seq (Op 0 (Halt (f s))) Nil).
                                         

    Definition wt_op_aux := wt_op_aux'.
    Definition wt_hnd_aux := wt_hnd_aux'.
    Definition wt_hnd_sym := wt_hnd_sym'.
    Definition react := react'.
  End Param.

  Module Import Semantics := Eff_Semantics(Param).
  
  Example prog0 : exp := With (Config (fun l => 0), []) (
                              0 # (Mov $0 5) ;;
                              0 # (Bop $1 Plus $0 $0) ;;
                              0 # (Ret $1) ;;
                              Nil
                              ).

  Goal wt_exp [H Exit] prog0 Bot.
  Proof. repeat (econstructor; eauto). instantiate (1:=0); simpl; constructor. Qed.
         

  Goal reduce prog0 (0 # (Halt 10) ;; Nil).
  Proof. repeat (econstructor; eauto; simpl). Qed.

  Example prog1 : exp := With (Config (fun l => 0), 
                               [ 0 # (Bop $3 Eq $0 $1) ;;
                                 0 # (Jz $3 1) ;;
                                 0 # (J 2) ;;
                                 Nil
                               ; 0 # (Bop $0 Plus $0 $4) ;;
                                 0 # (J 0) ;;
                                 Nil
                               ; 0 # (Ret $0) ;;
                                 Nil
                               ]) (
                               0 # (Mov $1 10) ;;
                               0 # (Mov $4 1) ;;
                               0 # (J 0) ;;
                               Nil
                               ).

                         
  Goal wt_exp [H Exit] prog1 Bot.
  Proof. unfold prog1. eapply wt_with with (th:=H (Cfg 3)); 
         repeat (econstructor; eauto). 
  Qed.

  Goal reduce prog1 (0 # (Halt 10) ;; Nil).
  Proof. repeat (econstructor; eauto; simpl). Qed.
    
  Example fib n : exp := With (Config (fun l => 0),
                              [ 0 # (Jz $0 1) ;;
                                0 # (Bop $0 Minus $0 $101) ;;
                                0 # (Bop $3 Plus $1 $2) ;;
                                0 # (Bop $1 Plus $2 $100) ;;
                                0 # (Bop $2 Plus $3 $100) ;;
                                0 # (J 0) ;;
                                Nil
                              ; 0 # (Ret $1) ;;
                                Nil 
                              ]) (
                              0 # (Mov $100 0) ;;
                              0 # (Mov $101 1) ;;
                              0 # (Mov $0 n) ;;
                              0 # (Mov $1 0) ;;
                              0 # (Mov $2 1) ;;
                              0 # (J 0) ;;
                              Nil
                              ).

  Goal forall n, wt_exp [H Exit] (fib n) Bot.
  Proof. unfold fib. intro. eapply wt_with with (th:=H (Cfg 2)); 
         repeat (econstructor; eauto). 
  Qed.

  (* slow! *)
  (* Goal reduce (fib 7) (0 # (Halt 13) ;; Nil). *)
  (* Proof. repeat (econstructor; eauto; simpl). Qed. *)

  Module Safety_Param <: EFF_SAFETY_PARAM.

    Lemma react_preservation : forall E Es o h ts th k es e,
      wt_hnd_aux h ts th ->
      wt_hnd_sym h th E Es ->
      Forall3 wt_exp Es es ts ->
      wt_exp (th::E) k Bot ->
      wt_op_aux o th ->
      react (h, es) o k e ->
      wt_exp E e Bot.
    Proof.
    (* exercise for the reader! *)
    Admitted.
      
    Lemma react_progress : forall E Es o h th es ts k,
      wt_hnd_aux h ts th ->
      wt_hnd_sym h th E Es ->
      Forall3 wt_exp Es es ts ->
      wt_op_aux o th ->
      exists e, react (h, es) o k e.
    Proof.
      intros. inversion H0; subst.
      inversion H3; subst;
      repeat (eexists; econstructor).
    Qed.

  End Safety_Param.

  Module Import Safety := Eff_Safety (Safety_Param).

End Assembly.