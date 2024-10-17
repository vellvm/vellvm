(* begin hide *)
From Coq Require Import
     Relations
     ZArith
     DecidableClass
     List
     String
     Bool.Bool
     Lia
     Program.Wf.

Import BinInt.

Require Import Ceres.Ceres.

Require Import Integers Floats.

From Flocq.IEEE754 Require Import
     Bits
     BinarySingleNaN
     Binary.

From ExtLib Require Import
     Core.RelDec
     Programming.Eqv
     Structures.Monads
     Data.Monads.EitherMonad
     Structures.Functor
     Data.Nat
     Data.List.

From Vellvm Require Import
     Utilities
     Syntax
     Semantics.MemoryAddress
     Semantics.Memory.Sizeof
     Semantics.VellvmIntegers
     Semantics.StoreId
     Utils.MapMonadExtra
     Utils.MonadEq1Laws
     Utils.MonadReturnsLaws
     QC.ShowAST.

Require Import Coq.Program.Equality.
Require Import Vellvm.Utils.VellvmRelations.

(* TODO: when/if we cut ties to QC, change this import *)
From QuickChick Require Import Show.
Import Monad.
Import EqvNotation.
Import MonadNotation.
Import ListNotations.
Import Logic.

Set Implicit Arguments.
Set Contextual Implicit.

Open Scope N_scope.
(* end hide *)

(** * Dynamic values
    Definition of the dynamic values manipulated by VIR.
    They come in two flavors:
    - [dvalue] are the concrete notion of values computed.
    - [uvalue] (_under-defined values_) are an extension of [dvalue] as symbolic values:
      + a special [undef τ] value modeling LLVM's "undef"
      + delayed numerical operations.
 *)

#[global] Instance Eqv_nat : Eqv nat := (@eq nat).

(* Floating-point rounding mode *)
Definition FT_Rounding:mode := mode_NE.

Definition inttyp (x:N) : Type :=
  match x with
  | 1 => int1
  | 8 => int8
  | 16 => int16
  | 32 => int32
  | 64 => int64
  | _ => False
  end.

(* TODO: This probably should live somewhere else... *)
#[refine]#[local] Instance Decidable_eq_N : forall (x y : N), Decidable (eq x y) := {
    Decidable_witness := N.eqb x y
  }.
apply N.eqb_eq.
Qed.

Definition ll_float  := Floats.float32.
Definition ll_double := Floats.float.

  (* TODO: Move this *)
  Lemma vector_dtyp_dec :
    forall t,
      {vector_dtyp t} + {~ vector_dtyp t}.
  Proof using.
    intros t.
    induction t;
      try
        solve
        [ left; constructor; eauto
        | left; firstorder
        | right;
          intros CONTRA;
          red in CONTRA;
          destruct CONTRA as [[n CONTRA] | CONTRA]; try discriminate;
          repeat (destruct CONTRA as [CONTRA | CONTRA]; try discriminate)
        ].
  Qed.


(* Sizeof is needed for for ConcatBytes case *)
Module DVALUE(A:Vellvm.Semantics.MemoryAddress.ADDRESS)(IP:Vellvm.Semantics.MemoryAddress.INTPTR)(SIZEOF:Sizeof).

  Import SIZEOF.
  Import IP.

  (* The set of dynamic values manipulated by an LLVM program. *)
  Unset Elimination Schemes.
  Inductive dvalue : Set :=
  | DVALUE_Addr (a:A.addr)
  | DVALUE_I (sz : positive) (x:@int sz)
  | DVALUE_IPTR (x:intptr)
  | DVALUE_Double (x:ll_double)
  | DVALUE_Float (x:ll_float)
  | DVALUE_Poison (t:dtyp)
  | DVALUE_Oom (t:dtyp)
  | DVALUE_None
  | DVALUE_Struct        (fields: list dvalue)
  | DVALUE_Packed_struct (fields: list dvalue)
  | DVALUE_Array         (t:dtyp) (elts: list dvalue)
  | DVALUE_Vector        (t:dtyp) (elts: list dvalue)
  .
  Set Elimination Schemes.

  Fixpoint show_dvalue (dv : dvalue) : string :=
    match dv with
    | DVALUE_Addr a => "<addr>"
    | DVALUE_I sz x => "i" ++ show (Zpos sz) ++ " " ++ show (unsigned x)
    | DVALUE_IPTR x => "<intptr>"
    | DVALUE_Double x => "double " ++ show x
    | DVALUE_Float x => "float " ++ show x
    | DVALUE_Poison t => "poison[" ++ show_dtyp t ++ "]"
    | DVALUE_Oom t => "oom[" ++ show_dtyp t ++ "]"
    | DVALUE_None => "none"
    | DVALUE_Struct fields => "{" ++ String.concat ", " (map show_dvalue fields) ++ "}"
    | DVALUE_Packed_struct fields => "{<" ++ String.concat ", " (map show_dvalue fields) ++ ">}"
    | DVALUE_Array _ elts => "["  ++ String.concat ", " (map show_dvalue elts) ++ "]"
    | DVALUE_Vector _ elts => "<"  ++ String.concat ", " (map show_dvalue elts) ++ ">"
    end.

  Fixpoint dvalue_measure (dv : dvalue) : nat :=
    match dv with
    | DVALUE_Addr a => 1
    | DVALUE_I sz x => 1
    | DVALUE_IPTR x => 1
    | DVALUE_Double x => 1
    | DVALUE_Float x => 1
    | DVALUE_Poison t => 1
    | DVALUE_Oom t => 1
    | DVALUE_None => 1
    | DVALUE_Struct fields => S (S (list_sum (map dvalue_measure fields)))
    | DVALUE_Packed_struct fields => S (S (list_sum (map dvalue_measure fields)))
    | DVALUE_Array t elts => S (S (list_sum (map dvalue_measure elts)))
    | DVALUE_Vector t elts => S (S (list_sum (map dvalue_measure elts)))
    end.

  Lemma dvalue_measure_gt_0 :
    forall (dv : dvalue),
      (0 < dvalue_measure dv)%nat.
  Proof using.
    destruct dv; cbn; auto.
    all: apply Nat.lt_0_succ.
  Qed.

  Ltac solve_dvalue_measure :=
    match goal with
    | Hin : In ?e ?fields |- context [dvalue_measure _]
      => pose proof list_sum_map dvalue_measure _ _ Hin;
        cbn; lia
    | H: Some ?f = List.nth_error ?fields _ |- context [dvalue_measure ?f]
      => symmetry in H; apply nth_error_In in H;
        pose proof list_sum_map dvalue_measure _ _ H;
        cbn; lia
    end.

  Inductive dvalue_direct_subterm : dvalue -> dvalue -> Prop :=
  | DVALUE_Struct_subterm : forall f fields, In f fields -> dvalue_direct_subterm f (DVALUE_Struct fields)
  | DVALUE_Packed_struct_subterm : forall f fields, In f fields -> dvalue_direct_subterm f (DVALUE_Packed_struct fields)
  | DVALUE_Array_subterm : forall t elt elts, In elt elts -> dvalue_direct_subterm elt (DVALUE_Array t elts)
  | DVALUE_Vector_subterm : forall t elt elts, In elt elts -> dvalue_direct_subterm elt (DVALUE_Vector t elts).

  Definition dvalue_strict_subterm := clos_trans _ dvalue_direct_subterm.
  Definition dvalue_subterm := clos_refl_trans _ dvalue_direct_subterm.

  Section DvalueInd.
    Variable P : dvalue -> Prop.
    Hypothesis IH_Addr          : forall a, P (DVALUE_Addr a).
    Hypothesis IH_I             : forall sz (x : @int sz), P (@DVALUE_I sz x).
    Hypothesis IH_IPTR          : forall x, P (DVALUE_IPTR x).
    Hypothesis IH_Double        : forall x, P (DVALUE_Double x).
    Hypothesis IH_Float         : forall x, P (DVALUE_Float x).
    Hypothesis IH_Poison        : forall t, P (DVALUE_Poison t).
    Hypothesis IH_Oom           : forall t, P (DVALUE_Oom t).
    Hypothesis IH_None          : P DVALUE_None.
    Hypothesis IH_Struct        : forall (fields: list dvalue), (forall u, In u fields -> P u) -> P (DVALUE_Struct fields).
    Hypothesis IH_Packed_Struct : forall (fields: list dvalue), (forall u, In u fields -> P u) -> P (DVALUE_Packed_struct fields).
    Hypothesis IH_Array         : forall t (elts: list dvalue), (forall e, In e elts -> P e) -> P (DVALUE_Array t elts).
    Hypothesis IH_Vector        : forall t (elts: list dvalue), (forall e, In e elts -> P e) -> P (DVALUE_Vector t elts).

    Lemma dvalue_ind : forall (dv:dvalue), P dv.
    Proof using All.
      fix IH 1.
      remember P as P0 in IH.
      destruct dv; auto; subst.
      - apply IH_Struct.
        { revert fields.
          fix IHfields 1. intros [|u fields']. intros. inversion H.
          intros u' [<-|Hin]. apply IH. eapply IHfields. apply Hin.
        }
      - apply IH_Packed_Struct.
        { revert fields.
          fix IHfields 1. intros [|u fields']. intros. inversion H.
          intros u' [<-|Hin]. apply IH. eapply IHfields. apply Hin.
        }
      - apply IH_Array.
        { revert elts.
          fix IHelts 1. intros [|u elts']. intros. inversion H.
          intros u' [<-|Hin]. apply IH. eapply IHelts. apply Hin.
        }
      - apply IH_Vector.
        { revert elts.
          fix IHelts 1. intros [|u elts']. intros. inversion H.
          intros u' [<-|Hin]. apply IH. eapply IHelts. apply Hin.
        }
    Qed.
  End DvalueInd.

  Section DvalueRec.
    Variable P : dvalue -> Set.
    Hypothesis IH_Addr          : forall a, P (DVALUE_Addr a).
    Hypothesis IH_I            : forall sz (x : @int sz), P (@DVALUE_I sz x).
    Hypothesis IH_IPTR           : forall x, P (DVALUE_IPTR x).
    Hypothesis IH_Double        : forall x, P (DVALUE_Double x).
    Hypothesis IH_Float         : forall x, P (DVALUE_Float x).
    Hypothesis IH_Poison        : forall t, P (DVALUE_Poison t).
    Hypothesis IH_Oom           : forall t, P (DVALUE_Oom t).
    Hypothesis IH_None          : P DVALUE_None.
    Hypothesis IH_Struct        : forall (fields: list dvalue), (forall u, InT u fields -> P u) -> P (DVALUE_Struct fields).
    Hypothesis IH_Packed_Struct : forall (fields: list dvalue), (forall u, InT u fields -> P u) -> P (DVALUE_Packed_struct fields).
    Hypothesis IH_Array         : forall t (elts: list dvalue), (forall e, InT e elts -> P e) -> P (DVALUE_Array t elts).
    Hypothesis IH_Vector        : forall t (elts: list dvalue), (forall e, InT e elts -> P e) -> P (DVALUE_Vector t elts).

    Lemma dvalue_rec : forall (dv:dvalue), P dv.
    Proof using All.
      fix IH 1.
      remember P as P0 in IH.
      destruct dv; auto; subst.
      - apply IH_Struct.
        { revert fields.
          fix IHfields 1. intros [|u fields']. intros. inversion X.
          intros u' [<-|Hin]. apply IH. eapply IHfields. apply Hin.
        }
      - apply IH_Packed_Struct.
        { revert fields.
          fix IHfields 1. intros [|u fields']. intros. inversion X.
          intros u' [<-|Hin]. apply IH. eapply IHfields. apply Hin.
        }
      - apply IH_Array.
        { revert elts.
          fix IHelts 1. intros [|u elts']. intros. inversion X.
          intros u' [<-|Hin]. apply IH. eapply IHelts. apply Hin.
        }
      - apply IH_Vector.
        { revert elts.
          fix IHelts 1. intros [|u elts']. intros. inversion X.
          intros u' [<-|Hin]. apply IH. eapply IHelts. apply Hin.
        }
    Qed.
  End DvalueRec.

  Lemma dvalue_strict_subterm_inv :
    forall x dv,
      dvalue_strict_subterm x dv ->
      exists s, dvalue_direct_subterm s dv /\ dvalue_subterm x s.
  Proof using.
    intros x dv H.
    eapply clos_t_rt_inv; auto.
  Qed.

  Lemma dvalue_direct_subterm_dvalue_measure :
    forall s e,
      dvalue_direct_subterm s e ->
      (dvalue_measure s < dvalue_measure e)%nat.
  Proof using.
    intros s e SUB.
    dependent induction SUB;
      solve_dvalue_measure.
  Qed.

  Lemma dvalue_subterm_antisymmetric :
    forall a b,
      dvalue_subterm a b ->
      dvalue_subterm b a ->
      a = b.
  Proof using.
    intros a b AB BA.
    eapply clos_refl_trans_antisymmetric with (m:=dvalue_measure); eauto.
    intros a0 b0 H.
    apply dvalue_direct_subterm_dvalue_measure; auto.
  Qed.

  Section DvalueStrongInd.
    Variable P : dvalue -> Prop.
    Hypothesis IH_Addr          : forall a, P (DVALUE_Addr a).
    Hypothesis IH_I             : forall sz (x : @int sz), P (@DVALUE_I sz x).
    Hypothesis IH_IPTR           : forall x, P (DVALUE_IPTR x).
    Hypothesis IH_Double        : forall x, P (DVALUE_Double x).
    Hypothesis IH_Float         : forall x, P (DVALUE_Float x).
    Hypothesis IH_Poison        : forall t, P (DVALUE_Poison t).
    Hypothesis IH_Oom           : forall t, P (DVALUE_Oom t).
    Hypothesis IH_None          : P DVALUE_None.
    Hypothesis IH_Subterm        : forall dv, (forall u, dvalue_strict_subterm u dv -> P u) -> P dv.

    Lemma dvalue_strong_ind : forall (dv:dvalue), P dv.
      intros dv.
      enough (IH : forall s, dvalue_subterm s dv -> P s).
      { apply IH. apply rt_refl. }

      induction dv;
        try solve
          [ (* Solve simple cases where there are no subterms *)
            match goal with
            | _ : _ |- forall s, dvalue_subterm s ?DV -> P s =>
                intros s H;
                assert (s = DV);
                [ dependent induction H; auto; inv H
                | subst; auto
                ]
            end

          | (* Solve structs *)
            intros s H';
            dependent induction H';
            [ (* rt_step *)
              match goal with
              | H: dvalue_direct_subterm ?x _,
                  IH : forall u : dvalue, In u _ -> forall s : dvalue, dvalue_subterm s u -> P s
                                                            |- P ?x =>
                  inv H;
                  apply IH_Subterm; eauto;
                  intros; eapply IH; eauto;
                  apply clos_t_rt; eauto
              end
            | (* rt_refl *)
              apply IH_Subterm;
              intros * STRICT;
              dependent induction STRICT;
              [ (* t_step *)
                match goal with
                | H: dvalue_direct_subterm ?x _,
                    IH : forall u : dvalue, In u _ -> forall s : dvalue, dvalue_subterm s u -> P s
                                                              |- P ?x =>
                    inv H;
                    eapply IH; eauto;
                    apply rt_refl
                end
              | (* t_trans *)
                match goal with
                | IH : forall u : dvalue, In u ?fields -> forall s : dvalue, dvalue_subterm s u -> P s
                                                            |- P ?x =>
                    clear IHSTRICT1;
                    specialize (IHSTRICT2 fields);
                    repeat (forward IHSTRICT2; auto);
                    pose proof t_trans _ _ _ _ _ STRICT1 STRICT2 as STRICT3;
                    eapply dvalue_strict_subterm_inv in STRICT3 as (s&DIRECT&SUB);
                    inv DIRECT;
                    eapply IH; eauto
                end
              ]
            | (* rt_trans *)
              match goal with
              | XY : clos_refl_trans dvalue dvalue_direct_subterm ?x ?y,
                  YZ : clos_refl_trans dvalue dvalue_direct_subterm ?y ?z,
                    IH : forall u : dvalue, In u _ -> forall s : dvalue, dvalue_subterm s u -> P s
                                                              |- _ =>
                  pose proof rt_trans _ _ _ _ _ XY YZ as XZ;
                  apply clos_rt_inv in XZ as [EQ | [w [R TRANS]]];
                  [ subst;
                    pose proof dvalue_subterm_antisymmetric XY YZ; subst; eauto
                  | inv R; eapply IH; eauto
                  ]
              end
            ]

          | (* Solve arrays / vectors *)
            intros t s H';
            dependent induction H';
            [ (* rt_step *)
              match goal with
              | H: dvalue_direct_subterm ?x _,
                  IH : forall u : dvalue, In u _ -> forall s : dvalue, dvalue_subterm s u -> P s
                                                            |- P ?x =>
                  inv H;
                  apply IH_Subterm; eauto;
                  intros; eapply IH; eauto;
                  apply clos_t_rt; eauto
              end
            | (* rt_refl *)
              apply IH_Subterm;
              intros * STRICT;
              dependent induction STRICT;
              [ (* t_step *)
                match goal with
                | H: dvalue_direct_subterm ?x _,
                    IH : forall u : dvalue, In u _ -> forall s : dvalue, dvalue_subterm s u -> P s
                                                              |- P ?x =>
                    inv H;
                    eapply IH; eauto;
                    apply rt_refl
                end
              | (* t_trans *)
                match goal with
                | IH : forall u : dvalue, In u ?fields -> forall s : dvalue, dvalue_subterm s u -> P s
                                                            |- P ?x =>
                    clear IHSTRICT1;
                    specialize (IHSTRICT2 t fields);
                    repeat (forward IHSTRICT2; auto);
                    pose proof t_trans _ _ _ _ _ STRICT1 STRICT2 as STRICT3;
                    eapply dvalue_strict_subterm_inv in STRICT3 as (s&DIRECT&SUB);
                    inv DIRECT;
                    eapply IH; eauto
                end
              ]
            | (* rt_trans *)
              match goal with
              | XY : clos_refl_trans dvalue dvalue_direct_subterm ?x ?y,
                  YZ : clos_refl_trans dvalue dvalue_direct_subterm ?y ?z,
                    IH : forall u : dvalue, In u _ -> forall s : dvalue, dvalue_subterm s u -> P s
                                                              |- _ =>
                  pose proof rt_trans _ _ _ _ _ XY YZ as XZ;
                  apply clos_rt_inv in XZ as [EQ | [w [R TRANS]]];
                  [ subst;
                    pose proof dvalue_subterm_antisymmetric XY YZ; subst; eauto
                  | inv R; eapply IH; eauto
                  ]
              end
            ]
          ].

      { intros s H'.
        dependent induction H'.
        - (* rt_step *)
          match goal with
          | H: dvalue_direct_subterm ?x _,
              IH : forall u : dvalue, In u _ -> forall s : dvalue, dvalue_subterm s u -> P s
                                                        |- P ?x =>
              inv H;
              apply IH_Subterm; eauto;
              intros; eapply IH; eauto;
              apply clos_t_rt; eauto
          end.
        - (* rt_refl *)
          apply IH_Subterm.
          intros * STRICT;
            dependent induction STRICT.
          + (* t_step *)
              match goal with
              | H: dvalue_direct_subterm ?x _,
                  IH : forall u : dvalue, In u _ -> forall s : dvalue, dvalue_subterm s u -> P s
                                                            |- P ?x =>
                  inv H;
                  eapply IH; eauto;
                  apply rt_refl
              end.
          + (* t_trans *)
            match goal with
            | IH : forall u : dvalue, In u ?fields -> forall s : dvalue, dvalue_subterm s u -> P s
                                                              |- P ?x =>
                clear IHSTRICT1;
                specialize (IHSTRICT2 t fields);
                repeat (forward IHSTRICT2; auto);
                pose proof t_trans _ _ _ _ _ STRICT1 STRICT2 as STRICT3;
                eapply dvalue_strict_subterm_inv in STRICT3 as (s&DIRECT&SUB);
                inv DIRECT;
                eapply IH; eauto
            end.
        - (* rt_trans *)
          match goal with
          | XY : clos_refl_trans dvalue dvalue_direct_subterm ?x ?y,
              YZ : clos_refl_trans dvalue dvalue_direct_subterm ?y ?z,
                IH : forall u : dvalue, In u _ -> forall s : dvalue, dvalue_subterm s u -> P s
                                                          |- _ =>
              pose proof rt_trans _ _ _ _ _ XY YZ as XZ;
              apply clos_rt_inv in XZ as [EQ | [w [R TRANS]]];
              [ subst;
                pose proof dvalue_subterm_antisymmetric XY YZ; subst; eauto
              | inv R; eapply IH; eauto
              ]
          end.
      }

      { intros s H'.
        dependent induction H'.
        - (* rt_step *)
          match goal with
          | H: dvalue_direct_subterm ?x _,
              IH : forall u : dvalue, In u _ -> forall s : dvalue, dvalue_subterm s u -> P s
                                                        |- P ?x =>
              inv H;
              apply IH_Subterm; eauto;
              intros; eapply IH; eauto;
              apply clos_t_rt; eauto
          end.
        - (* rt_refl *)
          apply IH_Subterm.
          intros * STRICT;
            dependent induction STRICT.
          + (* t_step *)
              match goal with
              | H: dvalue_direct_subterm ?x _,
                  IH : forall u : dvalue, In u _ -> forall s : dvalue, dvalue_subterm s u -> P s
                                                            |- P ?x =>
                  inv H;
                  eapply IH; eauto;
                  apply rt_refl
              end.
          + (* t_trans *)
            match goal with
            | IH : forall u : dvalue, In u ?fields -> forall s : dvalue, dvalue_subterm s u -> P s
                                                              |- P ?x =>
                clear IHSTRICT1;
                specialize (IHSTRICT2 t fields);
                repeat (forward IHSTRICT2; auto);
                pose proof t_trans _ _ _ _ _ STRICT1 STRICT2 as STRICT3;
                eapply dvalue_strict_subterm_inv in STRICT3 as (s&DIRECT&SUB);
                inv DIRECT;
                eapply IH; eauto
            end.
        - (* rt_trans *)
          match goal with
          | XY : clos_refl_trans dvalue dvalue_direct_subterm ?x ?y,
              YZ : clos_refl_trans dvalue dvalue_direct_subterm ?y ?z,
                IH : forall u : dvalue, In u _ -> forall s : dvalue, dvalue_subterm s u -> P s
                                                          |- _ =>
              pose proof rt_trans _ _ _ _ _ XY YZ as XZ;
              apply clos_rt_inv in XZ as [EQ | [w [R TRANS]]];
              [ subst;
                pose proof dvalue_subterm_antisymmetric XY YZ; subst; eauto
              | inv R; eapply IH; eauto
              ]
          end.
      }
    Qed.
  End DvalueStrongInd.

  (* The set of dynamic values manipulated by an LLVM program. *)
  Unset Elimination Schemes.
  Inductive uvalue : Type :=
  | UVALUE_Addr (a:A.addr)
  | UVALUE_I (sz : positive) (x:@int sz)
  | UVALUE_IPTR (x:intptr)
  | UVALUE_Double (x:ll_double)
  | UVALUE_Float (x:ll_float)
  | UVALUE_Undef (t:dtyp)
  | UVALUE_Poison (t:dtyp)
  | UVALUE_Oom (t:dtyp)
  | UVALUE_None
  | UVALUE_Struct        (fields: list uvalue)
  | UVALUE_Packed_struct (fields: list uvalue)
  | UVALUE_Array         (t : dtyp) (elts: list uvalue)
  | UVALUE_Vector        (t : dtyp) (elts: list uvalue)
  | UVALUE_IBinop           (iop:ibinop) (v1:uvalue) (v2:uvalue)
  | UVALUE_ICmp             (cmp:icmp)   (v1:uvalue) (v2:uvalue)
  | UVALUE_FBinop           (fop:fbinop) (fm:list fast_math) (v1:uvalue) (v2:uvalue)
  | UVALUE_FCmp             (cmp:fcmp)   (v1:uvalue) (v2:uvalue)
  | UVALUE_Conversion       (conv:conversion_type) (t_from:dtyp) (v:uvalue) (t_to:dtyp)
  | UVALUE_GetElementPtr    (t:dtyp) (ptrval:uvalue) (idxs:list (uvalue)) (* TODO: do we ever need this? GEP raises an event? *)
  | UVALUE_ExtractElement   (vec_typ : dtyp) (vec: uvalue) (idx: uvalue)
  | UVALUE_InsertElement    (vec_typ : dtyp) (vec: uvalue) (elt:uvalue) (idx:uvalue)
  | UVALUE_ShuffleVector    (vec_typ : dtyp) (vec1:uvalue) (vec2:uvalue) (idxmask:uvalue)
  | UVALUE_ExtractValue     (vec_typ : dtyp) (vec:uvalue) (idxs:list LLVMAst.int_ast)
  | UVALUE_InsertValue      (vec_typ : dtyp) (vec:uvalue) (elt_typ : dtyp) (elt:uvalue) (idxs:list LLVMAst.int_ast)
  | UVALUE_Select           (cnd:uvalue) (v1:uvalue) (v2:uvalue)
  (* Extract the `idx` byte from a uvalue `uv`, which was stored with
   type `dt`. `idx` 0 is the least significant byte. `sid` is the "store
   id". *)
  | UVALUE_ExtractByte      (uv : uvalue) (dt : dtyp) (idx : N) (sid : store_id)
  | UVALUE_ConcatBytes      (uvs : list uvalue) (dt : dtyp)
  .
  Set Elimination Schemes.

  Fixpoint uvalue_measure (uv : uvalue) : nat :=
    match uv with
    | UVALUE_Addr a => 1
    | UVALUE_I sz x => 1
    | UVALUE_IPTR x => 1
    | UVALUE_Double x => 1
    | UVALUE_Float x => 1
    | UVALUE_Undef t => 1
    | UVALUE_Poison t => 1
    | UVALUE_Oom t => 1
    | UVALUE_None => 1
    | UVALUE_Struct fields => S (S (list_sum (map uvalue_measure fields)))
    | UVALUE_Packed_struct fields => S (S (list_sum (map uvalue_measure fields)))
    | UVALUE_Array t elts => S (S (list_sum (map uvalue_measure elts)))
    | UVALUE_Vector t elts => S (S (list_sum (map uvalue_measure elts)))
    | UVALUE_IBinop _ v1 v2
    | UVALUE_ICmp _ v1 v2
    | UVALUE_FBinop _ _ v1 v2
    | UVALUE_FCmp _ v1 v2 =>
        S (uvalue_measure v1 + uvalue_measure v2)
    | UVALUE_Conversion conv t_from v t_to =>
        S (uvalue_measure v)
    | UVALUE_GetElementPtr t ptrval idxs =>
        S (uvalue_measure ptrval + list_sum (map uvalue_measure idxs))
    | UVALUE_ExtractElement t vec idx =>
        S (uvalue_measure vec + uvalue_measure idx)
    | UVALUE_InsertElement t vec elt idx =>
        S (uvalue_measure vec + uvalue_measure elt + uvalue_measure idx)
    | UVALUE_ShuffleVector t vec1 vec2 idxmask =>
        S (uvalue_measure vec1 + uvalue_measure vec2 + uvalue_measure idxmask)
    | UVALUE_ExtractValue t vec idxs =>
        S (uvalue_measure vec)
    | UVALUE_InsertValue t vec u elt idxs =>
        S (uvalue_measure vec + uvalue_measure elt)
    | UVALUE_Select cnd v1 v2 =>
        S (uvalue_measure cnd + uvalue_measure v1 + uvalue_measure v2)
    | UVALUE_ExtractByte uv dt idx sid =>
        S (uvalue_measure uv)
    | UVALUE_ConcatBytes uvs dt =>
        S (list_sum (map uvalue_measure uvs))
    end.

  Lemma uvalue_measure_gt_0 :
    forall (uv : uvalue),
      (0 < uvalue_measure uv)%nat.
  Proof using.
    destruct uv; cbn; auto.
    all: apply Nat.lt_0_succ.
  Qed.

  Ltac solve_dtyp_measure :=
    cbn;
    first [ lia
          | match goal with
            | _ : _ |- context [(dtyp_measure ?t + fold_right _ _ _)%nat]
              => pose proof (dtyp_measure_gt_0 t); unfold list_sum; lia
            end
          | match goal with
            | HIn : In ?x ?xs |- context [ list_sum (map ?f _)] =>
                pose proof (list_sum_map f x xs HIn)
            end;
            cbn in *; lia
      ].

  Ltac solve_uvalue_measure :=
    cbn;
    first [ lia
          | match goal with
            | _ : _ |- context [(uvalue_measure ?t + fold_right _ _ _)%nat]
              => pose proof (uvalue_measure_gt_0 t); unfold list_sum; lia
            end
          | match goal with
            | HIn : In ?x ?xs |- context [ list_sum (map ?f _)] =>
                pose proof (list_sum_map f x xs HIn)
            end;
            cbn in *; lia
      ].

  Ltac solve_uvalue_dtyp_measure :=
    red; cbn;
    repeat match goal with
           | Hin : In _ (repeatN _ _) |- _ =>
               apply In_repeatN in Hin; subst
           end;
    solve [ apply right_lex; solve_dtyp_measure
          | apply left_lex; solve_uvalue_measure
      ].


  Definition dvalue_is_poison (dv : dvalue) : bool :=
    match dv with
    | DVALUE_Poison dt => true
    | _ => false
    end.

  Definition uvalue_is_poison (uv : uvalue) : bool :=
    match uv with
    | UVALUE_Poison dt => true
    | _ => false
    end.

  Inductive uvalue_direct_subterm : uvalue -> uvalue -> Prop :=
  | UVALUE_Struct_subterm : forall f fields, In f fields -> uvalue_direct_subterm f (UVALUE_Struct fields)
  | UVALUE_Packed_struct_subterm : forall f fields, In f fields -> uvalue_direct_subterm f (UVALUE_Packed_struct fields)
  | UVALUE_Array_subterm : forall t elt elts, In elt elts -> uvalue_direct_subterm elt (UVALUE_Array t elts)
  | UVALUE_Vector_subterm : forall t elt elts, In elt elts -> uvalue_direct_subterm elt (UVALUE_Vector t elts)
  | UVALUE_IBinop_subterm_l : forall iop uv1 uv2, uvalue_direct_subterm uv1 (UVALUE_IBinop iop uv1 uv2)
  | UVALUE_IBinop_subterm_r : forall iop uv1 uv2, uvalue_direct_subterm uv2 (UVALUE_IBinop iop uv1 uv2)
  | UVALUE_ICmp_subterm_l : forall icmp uv1 uv2, uvalue_direct_subterm uv1 (UVALUE_ICmp icmp uv1 uv2)
  | UVALUE_ICmp_subterm_r : forall icmp uv1 uv2, uvalue_direct_subterm uv2 (UVALUE_ICmp icmp uv1 uv2)
  | UVALUE_FBinop_subterm_l : forall fop flags uv1 uv2, uvalue_direct_subterm uv1 (UVALUE_FBinop fop flags uv1 uv2)
  | UVALUE_FBinop_subterm_r : forall fop flags uv1 uv2, uvalue_direct_subterm uv2 (UVALUE_FBinop fop flags uv1 uv2)
  | UVALUE_FCmp_subterm_l : forall fcmp uv1 uv2, uvalue_direct_subterm uv1 (UVALUE_FCmp fcmp uv1 uv2)
  | UVALUE_FCmp_subterm_r : forall fcmp uv1 uv2, uvalue_direct_subterm uv2 (UVALUE_FCmp fcmp uv1 uv2)
  | UVALUE_Conversion_subterm : forall conv_type dt_from uv dt_to, uvalue_direct_subterm uv (UVALUE_Conversion conv_type dt_from uv dt_to)
  | UVALUE_GetElementPtr_subterm_addr : forall dt uv_addr uv_idxs, uvalue_direct_subterm uv_addr (UVALUE_GetElementPtr dt uv_addr uv_idxs)
  | UVALUE_GetElementPtr_subterm_idxs : forall dt uv_addr idx uv_idxs, In idx uv_idxs -> uvalue_direct_subterm idx (UVALUE_GetElementPtr dt uv_addr uv_idxs)
  | UVALUE_ExtractElement_subterm_vec : forall vec_typ vec idx, uvalue_direct_subterm vec (UVALUE_ExtractElement vec_typ vec idx)
  | UVALUE_ExtractElement_subterm_idx : forall vec_typ vec idx, uvalue_direct_subterm idx (UVALUE_ExtractElement vec_typ vec idx)
  | UVALUE_InsertElement_subterm_vec : forall vec_typ vec elt idx, uvalue_direct_subterm vec (UVALUE_InsertElement vec_typ vec elt idx)
  | UVALUE_InsertElement_subterm_elt : forall vec_typ vec elt idx, uvalue_direct_subterm elt (UVALUE_InsertElement vec_typ vec elt idx)
  | UVALUE_InsertElement_subterm_idx : forall vec_typ vec elt idx, uvalue_direct_subterm idx (UVALUE_InsertElement vec_typ vec elt idx)
  | UVALUE_ShuffleVector_subterm_vec1 : forall vec_typ vec1 vec2 idxmask, uvalue_direct_subterm vec1 (UVALUE_ShuffleVector vec_typ vec1 vec2 idxmask)
  | UVALUE_ShuffleVector_subterm_vec2 : forall vec_typ vec1 vec2 idxmask, uvalue_direct_subterm vec2 (UVALUE_ShuffleVector vec_typ vec1 vec2 idxmask)
  | UVALUE_ShuffleVector_subterm_idxmask : forall vec_typ vec1 vec2 idxmask, uvalue_direct_subterm idxmask (UVALUE_ShuffleVector vec_typ vec1 vec2 idxmask)
  | UVALUE_ExtractValue_subterm : forall vec_typ vec idxs, uvalue_direct_subterm vec (UVALUE_ExtractValue vec_typ vec idxs)
  | UVALUE_InsertValue_subterm_vec : forall vec_typ vec elt_typ elt idxs, uvalue_direct_subterm vec (UVALUE_InsertValue vec_typ vec elt_typ elt idxs)
  | UVALUE_InsertValue_subterm_elt : forall vec_typ vec elt_typ elt idxs, uvalue_direct_subterm elt (UVALUE_InsertValue vec_typ vec elt_typ elt idxs)
  | UVALUE_Select_subterm_cnd : forall cnd v1 v2, uvalue_direct_subterm cnd (UVALUE_Select cnd v1 v2)
  | UVALUE_Select_subterm_v1 : forall cnd v1 v2, uvalue_direct_subterm v1 (UVALUE_Select cnd v1 v2)
  | UVALUE_Select_subterm_v2 : forall cnd v1 v2, uvalue_direct_subterm v2 (UVALUE_Select cnd v1 v2)
  | UVALUE_ExtractByte_subterm : forall uv dt idx sid, uvalue_direct_subterm uv (UVALUE_ExtractByte uv dt idx sid)
  | UVALUE_ConcatBytes_subterm : forall dt uv uvs, In uv uvs -> uvalue_direct_subterm uv (UVALUE_ConcatBytes uvs dt).

  Definition uvalue_strict_subterm := clos_trans _ uvalue_direct_subterm.
  Definition uvalue_subterm := clos_refl_trans _ uvalue_direct_subterm.

  Section UvalueInd.
    Variable P : uvalue -> Prop.
    Hypothesis IH_Addr           : forall a, P (UVALUE_Addr a).
    Hypothesis IH_I              : forall sz x, P (@UVALUE_I sz x).
    Hypothesis IH_IPTR            : forall x, P (UVALUE_IPTR x).
    Hypothesis IH_Double         : forall x, P (UVALUE_Double x).
    Hypothesis IH_Float          : forall x, P (UVALUE_Float x).
    Hypothesis IH_Undef          : forall t, P (UVALUE_Undef t).
    Hypothesis IH_Poison         : forall t, P (UVALUE_Poison t).
    Hypothesis IH_Oom            : forall t, P (UVALUE_Oom t).
    Hypothesis IH_None           : P UVALUE_None.
    Hypothesis IH_Struct         : forall (fields: list uvalue), (forall u, In u fields -> P u) -> P (UVALUE_Struct fields).
    Hypothesis IH_Packed_Struct  : forall (fields: list uvalue), (forall u, In u fields -> P u) -> P (UVALUE_Packed_struct fields).
    Hypothesis IH_Array          : forall t (elts: list uvalue), (forall e, In e elts -> P e) -> P (UVALUE_Array t elts).
    Hypothesis IH_Vector         : forall t (elts: list uvalue), (forall e, In e elts -> P e) -> P (UVALUE_Vector t elts).
    Hypothesis IH_IBinop         : forall (iop:ibinop) (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_IBinop iop v1 v2).
    Hypothesis IH_ICmp           : forall (cmp:icmp)   (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_ICmp cmp v1 v2).
    Hypothesis IH_FBinop         : forall (fop:fbinop) (fm:list fast_math) (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_FBinop fop fm v1 v2).
    Hypothesis IH_FCmp           : forall (cmp:fcmp)   (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_FCmp cmp v1 v2).
    Hypothesis IH_Conversion     : forall (conv:conversion_type) (t_from:dtyp) (v:uvalue) (t_to:dtyp), P v -> P (UVALUE_Conversion conv t_from v t_to).
    Hypothesis IH_GetElementPtr  : forall (t:dtyp) (ptrval:uvalue) (idxs:list (uvalue)), P ptrval -> (forall idx, In idx idxs -> P idx) -> P (UVALUE_GetElementPtr t ptrval idxs).
    Hypothesis IH_ExtractElement : forall (t:dtyp) (vec: uvalue) (idx: uvalue), P vec -> P idx -> P (UVALUE_ExtractElement t vec idx).
    Hypothesis IH_InsertElement  : forall (t:dtyp) (vec: uvalue) (elt:uvalue) (idx:uvalue), P vec -> P elt -> P idx -> P (UVALUE_InsertElement t vec elt idx).
    Hypothesis IH_ShuffleVector  : forall (t:dtyp) (vec1:uvalue) (vec2:uvalue) (idxmask:uvalue), P vec1 -> P vec2 -> P idxmask -> P (UVALUE_ShuffleVector t vec1 vec2 idxmask).
    Hypothesis IH_ExtractValue   : forall (t:dtyp) (vec:uvalue) (idxs:list LLVMAst.int_ast), P vec -> P (UVALUE_ExtractValue t vec idxs).
    Hypothesis IH_InsertValue    : forall (t:dtyp) (vec:uvalue) (et:dtyp) (elt:uvalue) (idxs:list LLVMAst.int_ast), P vec -> P elt -> P (UVALUE_InsertValue t vec et elt idxs).
    Hypothesis IH_Select         : forall (cnd:uvalue) (v1:uvalue) (v2:uvalue), P cnd -> P v1 -> P v2 -> P (UVALUE_Select cnd v1 v2).
    Hypothesis IH_ExtractByte : forall (uv : uvalue) (dt : dtyp) (idx : N) (sid : N), P uv -> P (UVALUE_ExtractByte uv dt idx sid).
    Hypothesis IH_ConcatBytes : forall (dt : dtyp) (uvs : list uvalue),
        (forall u, In u uvs -> P u) ->
        P (UVALUE_ConcatBytes uvs dt).

    Lemma uvalue_ind : forall (uv:uvalue), P uv.
      fix IH 1.
      remember P as P0 in IH.
      destruct uv; auto; subst.
      - apply IH_Struct.
        { revert fields.
          fix IHfields 1. intros [|u fields']. intros. inversion H.
          intros u' [<-|Hin]. apply IH. eapply IHfields. apply Hin.
        }
      - apply IH_Packed_Struct.
        { revert fields.
          fix IHfields 1. intros [|u fields']. intros. inversion H.
          intros u' [<-|Hin]. apply IH. eapply IHfields. apply Hin.
        }
      - apply IH_Array.
        { revert elts.
          fix IHelts 1. intros [|u elts']. intros. inversion H.
          intros u' [<-|Hin]. apply IH. eapply IHelts. apply Hin.
        }
      - apply IH_Vector.
        { revert elts.
          fix IHelts 1. intros [|u elts']. intros. inversion H.
          intros u' [<-|Hin]. apply IH. eapply IHelts. apply Hin.
        }
      - apply IH_IBinop; auto.
      - apply IH_ICmp; auto.
      - apply IH_FBinop; auto.
      - apply IH_FCmp; auto.
      - apply IH_Conversion; auto.
      - apply IH_GetElementPtr. apply IH.
        { revert idxs.
          fix IHidxs 1. intros [|u idxs']. intros. inversion H.
          intros u' [<-|Hin]. apply IH. eapply IHidxs. apply Hin.
        }
      - apply IH_ExtractElement; auto.
      - apply IH_InsertElement; auto.
      - apply IH_ShuffleVector; auto.
      - apply IH_ExtractValue; auto.
      - apply IH_InsertValue; auto.
      - apply IH_Select; auto.
      - apply IH_ExtractByte; auto.
      - apply IH_ConcatBytes.
        { revert uvs.
          fix IHuvs 1. intros [|u uvs']. intros. inversion H.
          intros u' [<-|Hin]. apply IH. eapply IHuvs. apply Hin.
        }
    Qed.
  End UvalueInd.

  Lemma uvalue_strict_subterm_inv :
    forall x dv,
      uvalue_strict_subterm x dv ->
      exists s, uvalue_direct_subterm s dv /\ uvalue_subterm x s.
  Proof using.
    intros x dv H.
    eapply clos_t_rt_inv; auto.
  Qed.

  Lemma uvalue_concat_bytes_strict_subterm :
    forall u uv_bytes dt,
      Exists (uvalue_subterm u) uv_bytes ->
      uvalue_strict_subterm u (UVALUE_ConcatBytes uv_bytes dt).
  Proof using.
    intros u uv_bytes dt H. generalize dependent dt.
    induction H.
    { unfold uvalue_subterm in H. unfold uvalue_strict_subterm.
      (* The idea here: if uvalue_direct_subterm is refl, then clos_trans is transitive with x and x is *)
      intros.
      eapply clos_rt_t.
      - apply H.
      - apply t_step; constructor; apply in_eq. }
    { intros dt. apply Exists_In in H.
      destruct H as (a&H1&H2).
      unfold uvalue_subterm in H2. unfold uvalue_strict_subterm.
      eapply clos_rt_t.
      apply H2.
      apply t_step. constructor. simpl. right. assumption.
    }
  Qed.

  Lemma uvalue_getelementptr_strict_subterm :
    forall u idxs addr t,
      Exists (uvalue_subterm u) idxs ->
      uvalue_strict_subterm u (UVALUE_GetElementPtr t addr idxs).
  Proof using.
    intros u idxs addr t H.
    generalize dependent t.
    induction H.
    { unfold uvalue_subterm in H. unfold uvalue_strict_subterm.
      (* The idea here: if uvalue_direct_subterm is refl, then clos_trans is transitive with x and x is *)
      intros.
      eapply clos_rt_t.
      - apply H.
      - apply t_step; constructor; apply in_eq. }
    { intros dt. apply Exists_In in H.
      destruct H as (a&H1&H2).
      unfold uvalue_subterm in H2. unfold uvalue_strict_subterm.
      eapply clos_rt_t.
      apply H2.
      apply t_step. constructor. simpl. right. assumption.
    }
  Qed.

  Lemma uvalue_struct_strict_subterm :
    forall u uvs,
      Exists (uvalue_subterm u) uvs ->
      uvalue_strict_subterm u (UVALUE_Struct uvs).
  Proof using.
    intros u uvs H.
    induction H.
    { unfold uvalue_subterm in H. unfold uvalue_strict_subterm.
      (* The idea here: if uvalue_direct_subterm is refl, then clos_trans is transitive with x and x is *)
      intros.
      eapply clos_rt_t.
      - apply H.
      - apply t_step; constructor; apply in_eq. }
    { apply Exists_In in H.
      destruct H as (a&H1&H2).
      unfold uvalue_subterm in H2. unfold uvalue_strict_subterm.
      eapply clos_rt_t.
      apply H2.
      apply t_step. constructor. simpl. right. assumption.
    }
  Qed.

  Lemma uvalue_packed_struct_strict_subterm :
    forall u uvs,
      Exists (uvalue_subterm u) uvs ->
      uvalue_strict_subterm u (UVALUE_Packed_struct uvs).
  Proof using.
    intros u uvs H.
    induction H.
    { unfold uvalue_subterm in H. unfold uvalue_strict_subterm.
      (* The idea here: if uvalue_direct_subterm is refl, then clos_trans is transitive with x and x is *)
      intros.
      eapply clos_rt_t.
      - apply H.
      - apply t_step; constructor; apply in_eq. }
    { apply Exists_In in H.
      destruct H as (a&H1&H2).
      unfold uvalue_subterm in H2. unfold uvalue_strict_subterm.
      eapply clos_rt_t.
      apply H2.
      apply t_step. constructor. simpl. right. assumption.
    }
  Qed.

  Lemma uvalue_array_strict_subterm :
    forall t u uvs,
      Exists (uvalue_subterm u) uvs ->
      uvalue_strict_subterm u (UVALUE_Array t uvs).
  Proof using.
    intros t u uvs H.
    induction H.
    { unfold uvalue_subterm in H. unfold uvalue_strict_subterm.
      (* The idea here: if uvalue_direct_subterm is refl, then clos_trans is transitive with x and x is *)
      intros.
      eapply clos_rt_t.
      - apply H.
      - apply t_step; constructor; apply in_eq. }
    { apply Exists_In in H.
      destruct H as (a&H1&H2).
      unfold uvalue_subterm in H2. unfold uvalue_strict_subterm.
      eapply clos_rt_t.
      apply H2.
      apply t_step. constructor. simpl. right. assumption.
    }
  Qed.

  Lemma uvalue_vector_strict_subterm :
    forall t u uvs,
      Exists (uvalue_subterm u) uvs ->
      uvalue_strict_subterm u (UVALUE_Vector t uvs).
  Proof using.
    intros t u uvs H.
    induction H.
    { unfold uvalue_subterm in H. unfold uvalue_strict_subterm.
      (* The idea here: if uvalue_direct_subterm is refl, then clos_trans is transitive with x and x is *)
      intros.
      eapply clos_rt_t.
      - apply H.
      - apply t_step; constructor; apply in_eq. }
    { apply Exists_In in H.
      destruct H as (a&H1&H2).
      unfold uvalue_subterm in H2. unfold uvalue_strict_subterm.
      eapply clos_rt_t.
      apply H2.
      apply t_step. constructor. simpl. right. assumption.
    }
  Qed.

  Lemma uvalue_direct_subterm_uvalue_measure :
    forall s e,
      uvalue_direct_subterm s e ->
      (uvalue_measure s < uvalue_measure e)%nat.
  Proof using.
    intros s e SUB.
    dependent induction SUB;
      solve_uvalue_measure.
  Qed.

  Lemma uvalue_subterm_antisymmetric :
    forall a b,
      uvalue_subterm a b ->
      uvalue_subterm b a ->
      a = b.
  Proof using.
    intros a b AB BA.
    eapply clos_refl_trans_antisymmetric with (m:=uvalue_measure); eauto.
    intros a0 b0 H.
    apply uvalue_direct_subterm_uvalue_measure; auto.
  Qed.

  Section UvalueStrongInd.
    Variable P : uvalue -> Prop.
    Hypothesis IH_Base : forall y, (forall x, ~ uvalue_direct_subterm x y) -> P y.
    Hypothesis IH_Subterm : forall uv, (forall u, uvalue_strict_subterm u uv -> P u) -> P uv.

    Lemma uvalue_strong_ind' : forall (uv:uvalue), P uv.
      intros uv.
      enough (IH : forall s, uvalue_subterm s uv -> P s).
      { apply IH. apply rt_refl. }

      induction uv;
        try solve
          [ (* Solve simple cases where there are no subterms *)
            intros s SUB;
            inv SUB;
            solve
              [
                match goal with
                | H : uvalue_direct_subterm _ _ |- _ =>
                    inv H
                end
              | apply IH_Base;
                intros ? CONTRA; inv CONTRA
              | apply IH_Subterm;
                intros * STRICT;
                match goal with
                | SUB1 : clos_refl_trans uvalue uvalue_direct_subterm ?x ?y,
                    SUB2 : clos_refl_trans uvalue uvalue_direct_subterm ?y ?z,
                      STRICT : uvalue_strict_subterm ?u ?x |- _ =>
                    assert (uvalue_strict_subterm u z) as STRICT';
                    [ eapply clos_t_rt_t; eauto;
                      eapply rt_trans; eauto
                    | clear STRICT; rename STRICT' into STRICT;
                      dependent induction STRICT;
                      [ (* t_step *)
                        match goal with
                        | H: uvalue_direct_subterm _ _ |- _ =>
                            solve [inv H]
                        end
                      | (* t_trans *)
                        pose proof t_trans _ _ _ _ _ STRICT1 STRICT2 as STRICT3;
                        eapply uvalue_strict_subterm_inv in STRICT3 as (s'&DIRECT&SUB);
                        inv DIRECT
                      ]
                    ]
                end
              ]

          | (* Solve structs and arrays *)
            intros s H';
            dependent induction H';
            [ (* rt_step *)
              match goal with
              | H: uvalue_direct_subterm ?x _,
                  IH : forall u : uvalue, In u _ -> forall s : uvalue, uvalue_subterm s u -> P s
                                                            |- P ?x =>
                  inv H;
                  apply IH_Subterm; eauto;
                  intros; eapply IH; eauto;
                  apply clos_t_rt; eauto
              end
            | (* rt_refl *)
              apply IH_Subterm;
              intros * STRICT;
              dependent induction STRICT;
              [ (* t_step *)
                match goal with
                | H: uvalue_direct_subterm ?x _,
                    IH : forall u : uvalue, In u _ -> forall s : uvalue, uvalue_subterm s u -> P s
                                                              |- P ?x =>
                    inv H;
                    eapply IH; eauto;
                    apply rt_refl
                end
              | (* t_trans *)
                match goal with
                | IH : forall u : uvalue, In u ?fields -> forall s : uvalue, uvalue_subterm s u -> P s
                                                                  |- P ?x =>
                    clear IHSTRICT1;
                    specialize (IHSTRICT2 fields);
                    repeat (forward IHSTRICT2; auto);
                    pose proof t_trans _ _ _ _ _ STRICT1 STRICT2 as STRICT3;
                    eapply uvalue_strict_subterm_inv in STRICT3 as (s&DIRECT&SUB);
                    inv DIRECT;
                    eapply IH; eauto
                end
              ]
            | (* rt_trans *)
              match goal with
              | XY : clos_refl_trans uvalue uvalue_direct_subterm ?x ?y,
                  YZ : clos_refl_trans uvalue uvalue_direct_subterm ?y ?z,
                    IH : forall u : uvalue, In u _ -> forall s : uvalue, uvalue_subterm s u -> P s
                                                              |- _ =>
                  pose proof rt_trans _ _ _ _ _ XY YZ as XZ;
                  apply clos_rt_inv in XZ as [EQ | [w [R TRANS]]];
                  [ subst;
                    pose proof uvalue_subterm_antisymmetric XY YZ; subst; eauto
                  | inv R; eapply IH; eauto
                  ]
              end
            ]
          | (* Solve operations with 3 uvalues *)
            intros s H';
            dependent induction H';
            [ (* rt_step *)
              match goal with
              | H: uvalue_direct_subterm ?x _,
                  IHuv1 : forall s : uvalue, uvalue_subterm s ?uv1 -> P s,
                IHuv2 : forall s : uvalue, uvalue_subterm s ?uv2 -> P s,
                IHuv3 : forall s : uvalue, uvalue_subterm s ?uv3 -> P s
                                      |- P ?x =>
                inv H;
                apply IH_Subterm; eauto;
                [ intros; eapply IHuv1; eauto;
                  apply clos_t_rt; eauto
                | intros; eapply IHuv2; eauto;
                  apply clos_t_rt; eauto
                | intros; eapply IHuv3; eauto;
                  apply clos_t_rt; eauto
                ]
              end
            | (* rt_refl *)
              eapply IH_Subterm;
              intros * STRICT;
              dependent induction STRICT;
              [ (* t_step *)
                match goal with
                | H: uvalue_direct_subterm ?x _,
                    IHuv1 : forall s : uvalue, uvalue_subterm s ?uv1 -> P s,
                  IHuv2 : forall s : uvalue, uvalue_subterm s ?uv2 -> P s,
                  IHuv3 : forall s : uvalue, uvalue_subterm s ?uv3 -> P s
                                        |- P ?x =>
                  inv H;
                  [ eapply IHuv1; apply rt_refl
                  | eapply IHuv2; apply rt_refl
                  | eapply IHuv3; apply rt_refl
                  ]
                end
              | pose proof t_trans _ _ _ _ _ STRICT1 STRICT2 as STRICT3;
                eapply uvalue_strict_subterm_inv in STRICT3 as (s&DIRECT&SUB);
                inv DIRECT;
                [ eapply IHuv1; eauto
                | eapply IHuv2; eauto
                | eapply IHuv3; eauto
                ]
              ]
            | (* rt_trans *)
              match goal with
              | XY : clos_refl_trans uvalue uvalue_direct_subterm ?x ?y,
                  YZ : clos_refl_trans uvalue uvalue_direct_subterm ?y ?z,
                    IHuv1 : forall s : uvalue, uvalue_subterm s ?uv1 -> P s,
                IHuv2 : forall s : uvalue, uvalue_subterm s ?uv2 -> P s,
                IHuv3 : forall s : uvalue, uvalue_subterm s ?uv3 -> P s
                                      |- _ =>
                pose proof rt_trans _ _ _ _ _ XY YZ as XZ;
                apply clos_rt_inv in XZ as [EQ | [w [R TRANS]]];
                [ subst;
                  pose proof uvalue_subterm_antisymmetric XY YZ; subst; eauto
                | inv R;
                  [ eapply IHuv1; eauto
                  | eapply IHuv2; eauto
                  | eapply IHuv3; eauto
                  ]
                ]
              end
            ]
          | (* Solve binops *)
            intros s H';
            dependent induction H';
            [ (* rt_step *)
              match goal with
              | H: uvalue_direct_subterm ?x _,
                  IHuv1 : forall s : uvalue, uvalue_subterm s ?uv1 -> P s,
                IHuv2 : forall s : uvalue, uvalue_subterm s ?uv2 -> P s
                                      |- P ?x =>
                inv H;
                apply IH_Subterm; eauto;
                [ intros; eapply IHuv1; eauto;
                  apply clos_t_rt; eauto
                | intros; eapply IHuv2; eauto;
                  apply clos_t_rt; eauto
                ]
              end
            | (* rt_refl *)
              eapply IH_Subterm;
              intros * STRICT;
              dependent induction STRICT;
              [ (* t_step *)
                match goal with
                | H: uvalue_direct_subterm ?x _,
                    IHuv1 : forall s : uvalue, uvalue_subterm s ?uv1 -> P s,
                  IHuv2 : forall s : uvalue, uvalue_subterm s ?uv2 -> P s
                                        |- P ?x =>
                  inv H;
                  [ eapply IHuv1; apply rt_refl
                  | eapply IHuv2; apply rt_refl
                  ]
                end
              | pose proof t_trans _ _ _ _ _ STRICT1 STRICT2 as STRICT3;
                eapply uvalue_strict_subterm_inv in STRICT3 as (s&DIRECT&SUB);
                inv DIRECT;
                [ eapply IHuv1; eauto
                | eapply IHuv2; eauto
                ]
              ]
            | (* rt_trans *)
              match goal with
              | XY : clos_refl_trans uvalue uvalue_direct_subterm ?x ?y,
                  YZ : clos_refl_trans uvalue uvalue_direct_subterm ?y ?z
                |- _ =>
                  pose proof rt_trans _ _ _ _ _ XY YZ as XZ;
                  apply clos_rt_inv in XZ as [EQ | [w [R TRANS]]];
                  [ subst;
                    pose proof uvalue_subterm_antisymmetric XY YZ; subst; eauto
                  | inv R;
                    [ eapply IHuv1; eauto
                    | eapply IHuv2; eauto
                    ]
                  ]
              end
            ]
          | (* Solve single subterm *)
            intros s H';
            dependent induction H';
            [ (* rt_step *)
              match goal with
              | H: uvalue_direct_subterm ?x _,
                  IHuv : forall s : uvalue, uvalue_subterm s ?uv1 -> P s
                                       |- P ?x =>
                  inv H;
                  apply IH_Subterm; eauto;
                  intros; eapply IHuv; eauto;
                  apply clos_t_rt; eauto
              end
            | (* rt_refl *)
              eapply IH_Subterm;
              intros * STRICT;
              dependent induction STRICT;
              [ (* t_step *)
                match goal with
                | H: uvalue_direct_subterm ?x _,
                    IHuv : forall s : uvalue, uvalue_subterm s ?uv1 -> P s
                                         |- P ?x =>
                    inv H;
                    eapply IHuv; apply rt_refl
                end
              | pose proof t_trans _ _ _ _ _ STRICT1 STRICT2 as STRICT3;
                eapply uvalue_strict_subterm_inv in STRICT3 as (s&DIRECT&SUB);
                inv DIRECT;
                eapply IHuv; eauto
              ]
            | (* rt_trans *)
              match goal with
              | XY : clos_refl_trans uvalue uvalue_direct_subterm ?x ?y,
                  YZ : clos_refl_trans uvalue uvalue_direct_subterm ?y ?z,
                    IHuv : forall s : uvalue, uvalue_subterm s ?uv1 -> P s
                                         |- _ =>
                  pose proof rt_trans _ _ _ _ _ XY YZ as XZ;
                  apply clos_rt_inv in XZ as [EQ | [w [R TRANS]]];
                  [ subst;
                    pose proof uvalue_subterm_antisymmetric XY YZ; subst; eauto
                  | inv R;
                    eapply IHuv; eauto
                  ]
              end
            ]
          ].

      { intros s H'.
        dependent induction H'.
        - (* rt_step *)
          match goal with
          | H: uvalue_direct_subterm ?x _,
              IH : forall u : uvalue, In u _ -> forall s : uvalue, uvalue_subterm s u -> P s
                                                        |- P ?x =>
              inv H;
              apply IH_Subterm; eauto;
              intros; eapply IH; eauto;
              apply clos_t_rt; eauto
          end.
        - (* rt_refl *)
          apply IH_Subterm.
          intros * STRICT;
            dependent induction STRICT.
          + (* t_step *)
              match goal with
              | H: uvalue_direct_subterm ?x _,
                  IH : forall u : uvalue, In u _ -> forall s : uvalue, uvalue_subterm s u -> P s
                                                            |- P ?x =>
                  inv H;
                  eapply IH; eauto;
                  apply rt_refl
              end.
          + (* t_trans *)
            match goal with
            | IH : forall u : uvalue, In u ?fields -> forall s : uvalue, uvalue_subterm s u -> P s
                                                              |- P ?x =>
                clear IHSTRICT1;
                specialize (IHSTRICT2 t fields);
                repeat (forward IHSTRICT2; auto);
                pose proof t_trans _ _ _ _ _ STRICT1 STRICT2 as STRICT3;
                eapply uvalue_strict_subterm_inv in STRICT3 as (s&DIRECT&SUB);
                inv DIRECT;
                eapply IH; eauto
            end.
        - (* rt_trans *)
          match goal with
          | XY : clos_refl_trans uvalue uvalue_direct_subterm ?x ?y,
              YZ : clos_refl_trans uvalue uvalue_direct_subterm ?y ?z,
                IH : forall u : uvalue, In u _ -> forall s : uvalue, uvalue_subterm s u -> P s
                                                          |- _ =>
              pose proof rt_trans _ _ _ _ _ XY YZ as XZ;
              apply clos_rt_inv in XZ as [EQ | [w [R TRANS]]];
              [ subst;
                pose proof uvalue_subterm_antisymmetric XY YZ; subst; eauto
              | inv R; eapply IH; eauto
              ]
          end.
      }

      { intros s H'.
        dependent induction H'.
        - (* rt_step *)
          match goal with
          | H: uvalue_direct_subterm ?x _,
              IH : forall u : uvalue, In u _ -> forall s : uvalue, uvalue_subterm s u -> P s
                                                        |- P ?x =>
              inv H;
              apply IH_Subterm; eauto;
              intros; eapply IH; eauto;
              apply clos_t_rt; eauto
          end.
        - (* rt_refl *)
          apply IH_Subterm.
          intros * STRICT;
            dependent induction STRICT.
          + (* t_step *)
              match goal with
              | H: uvalue_direct_subterm ?x _,
                  IH : forall u : uvalue, In u _ -> forall s : uvalue, uvalue_subterm s u -> P s
                                                            |- P ?x =>
                  inv H;
                  eapply IH; eauto;
                  apply rt_refl
              end.
          + (* t_trans *)
            match goal with
            | IH : forall u : uvalue, In u ?fields -> forall s : uvalue, uvalue_subterm s u -> P s
                                                              |- P ?x =>
                clear IHSTRICT1;
                specialize (IHSTRICT2 t fields);
                repeat (forward IHSTRICT2; auto);
                pose proof t_trans _ _ _ _ _ STRICT1 STRICT2 as STRICT3;
                eapply uvalue_strict_subterm_inv in STRICT3 as (s&DIRECT&SUB);
                inv DIRECT;
                eapply IH; eauto
            end.
        - (* rt_trans *)
          match goal with
          | XY : clos_refl_trans uvalue uvalue_direct_subterm ?x ?y,
              YZ : clos_refl_trans uvalue uvalue_direct_subterm ?y ?z,
                IH : forall u : uvalue, In u _ -> forall s : uvalue, uvalue_subterm s u -> P s
                                                          |- _ =>
              pose proof rt_trans _ _ _ _ _ XY YZ as XZ;
              apply clos_rt_inv in XZ as [EQ | [w [R TRANS]]];
              [ subst;
                pose proof uvalue_subterm_antisymmetric XY YZ; subst; eauto
              | inv R; eapply IH; eauto
              ]
          end.
      }

      { (* GEP *)
        intros s H';
          dependent induction H'.
        - (* rt_step *)
          inv H0.
          + (* addr *)
            eapply IHuv; apply rt_refl.
          + (* idxs *)
            eapply H; eauto.
            apply rt_refl.
        - (* rt_refl *)
          apply IH_Subterm;
            intros * STRICT;
            dependent induction STRICT.
          + (* t_step *)
            inv H0.
            * (* addr *)
              eapply IHuv; apply rt_refl.
            * (* idxs *)
              eapply H; eauto.
              apply rt_refl.
          + (* t_trans *)
            pose proof t_trans _ _ _ _ _ STRICT1 STRICT2 as STRICT3;
              eapply uvalue_strict_subterm_inv in STRICT3 as (s&DIRECT&SUB);
              inv DIRECT.
            * eapply IHuv; eauto.
            * eapply H; eauto.
        - (* rt_trans *)
          pose proof rt_trans _ _ _ _ _ H'1 H'2 as XZ;
            apply clos_rt_inv in XZ as [EQ | [w [R TRANS]]];
            [ subst;
              pose proof uvalue_subterm_antisymmetric H'1 H'2; subst; eauto
            |
            ].

          inv R;
            [ eapply IHuv; eauto
            | eapply H; eauto
            ].
      }

      { (* ConcatBytes *)
        intros s H';
          dependent induction H'.
        - (* rt_step *)
          inv H0.
          eapply H; eauto; apply rt_refl.
        - (* rt_refl *)
          apply IH_Subterm;
            intros * STRICT;
            dependent induction STRICT.
          + (* t_step *)
            inv H0.
            eapply H; eauto.
            apply rt_refl.
          + (* t_trans *)
            pose proof t_trans _ _ _ _ _ STRICT1 STRICT2 as STRICT3;
              eapply uvalue_strict_subterm_inv in STRICT3 as (s&DIRECT&SUB);
              inv DIRECT.
            * eapply H; eauto.
        - (* rt_trans *)
          pose proof rt_trans _ _ _ _ _ H'1 H'2 as XZ;
            apply clos_rt_inv in XZ as [EQ | [w [R TRANS]]];
            [ subst;
              pose proof uvalue_subterm_antisymmetric H'1 H'2; subst; eauto
            |
            ].

          inv R;
            eapply H; eauto.
      }
    Qed.
  End UvalueStrongInd.

  Section UvalueStrongInd.
    Variable P : uvalue -> Prop.
    Hypothesis IH_Addr           : forall a, P (UVALUE_Addr a).
    Hypothesis IH_I              : forall sz x, P (@UVALUE_I sz x).
    Hypothesis IH_IPTR            : forall x, P (UVALUE_IPTR x).
    Hypothesis IH_Double         : forall x, P (UVALUE_Double x).
    Hypothesis IH_Float          : forall x, P (UVALUE_Float x).
    Hypothesis IH_Undef          : forall t, P (UVALUE_Undef t).
    Hypothesis IH_Poison         : forall t, P (UVALUE_Poison t).
    Hypothesis IH_Oom            : forall t, P (UVALUE_Oom t).
    Hypothesis IH_None           : P UVALUE_None.
    Hypothesis IH_Subterm        : forall uv, (forall u, uvalue_strict_subterm u uv -> P u) -> P uv.

    Lemma uvalue_strong_ind : forall (uv:uvalue), P uv.
      intros uv.
      enough (IH : forall s, uvalue_subterm s uv -> P s).
      { apply IH. apply rt_refl. }

      induction uv;
        try solve
          [ (* Solve simple cases where there are no subterms *)
            match goal with
            | _ : _ |- forall s, uvalue_subterm s ?UV -> P s =>
                intros s H;
                assert (s = UV);
                [ dependent induction H; auto; inv H
                | subst; auto
                ]
            end

          | (* Solve structs and arrays *)
            intros s H';
            dependent induction H';
            [ (* rt_step *)
              match goal with
              | H: uvalue_direct_subterm ?x _,
                  IH : forall u : uvalue, In u _ -> forall s : uvalue, uvalue_subterm s u -> P s
                                                            |- P ?x =>
                  inv H;
                  apply IH_Subterm; eauto;
                  intros; eapply IH; eauto;
                  apply clos_t_rt; eauto
              end
            | (* rt_refl *)
              apply IH_Subterm;
              intros * STRICT;
              dependent induction STRICT;
              [ (* t_step *)
                match goal with
                | H: uvalue_direct_subterm ?x _,
                    IH : forall u : uvalue, In u _ -> forall s : uvalue, uvalue_subterm s u -> P s
                                                              |- P ?x =>
                    inv H;
                    eapply IH; eauto;
                    apply rt_refl
                end
              | (* t_trans *)
                match goal with
                | IH : forall u : uvalue, In u ?fields -> forall s : uvalue, uvalue_subterm s u -> P s
                                                            |- P ?x =>
                    clear IHSTRICT1;
                    specialize (IHSTRICT2 fields);
                    repeat (forward IHSTRICT2; auto);
                    pose proof t_trans _ _ _ _ _ STRICT1 STRICT2 as STRICT3;
                    eapply uvalue_strict_subterm_inv in STRICT3 as (s&DIRECT&SUB);
                    inv DIRECT;
                    eapply IH; eauto
                end
              ]
            | (* rt_trans *)
              match goal with
              | XY : clos_refl_trans uvalue uvalue_direct_subterm ?x ?y,
                  YZ : clos_refl_trans uvalue uvalue_direct_subterm ?y ?z,
                    IH : forall u : uvalue, In u _ -> forall s : uvalue, uvalue_subterm s u -> P s
                                                              |- _ =>
                  pose proof rt_trans _ _ _ _ _ XY YZ as XZ;
                  apply clos_rt_inv in XZ as [EQ | [w [R TRANS]]];
                  [ subst;
                    pose proof uvalue_subterm_antisymmetric XY YZ; subst; eauto
                  | inv R; eapply IH; eauto
                  ]
              end
            ]
          | (* Solve operations with 3 uvalues *)
            intros s H';
            dependent induction H';
            [ (* rt_step *)
              match goal with
              | H: uvalue_direct_subterm ?x _,
                  IHuv1 : forall s : uvalue, uvalue_subterm s ?uv1 -> P s,
                IHuv2 : forall s : uvalue, uvalue_subterm s ?uv2 -> P s,
                IHuv3 : forall s : uvalue, uvalue_subterm s ?uv3 -> P s
                                      |- P ?x =>
                inv H;
                apply IH_Subterm; eauto;
                [ intros; eapply IHuv1; eauto;
                  apply clos_t_rt; eauto
                | intros; eapply IHuv2; eauto;
                  apply clos_t_rt; eauto
                | intros; eapply IHuv3; eauto;
                  apply clos_t_rt; eauto
                ]
              end
            | (* rt_refl *)
              eapply IH_Subterm;
              intros * STRICT;
              dependent induction STRICT;
              [ (* t_step *)
                match goal with
                | H: uvalue_direct_subterm ?x _,
                    IHuv1 : forall s : uvalue, uvalue_subterm s ?uv1 -> P s,
                  IHuv2 : forall s : uvalue, uvalue_subterm s ?uv2 -> P s,
                  IHuv3 : forall s : uvalue, uvalue_subterm s ?uv3 -> P s
                                        |- P ?x =>
                  inv H;
                  [ eapply IHuv1; apply rt_refl
                  | eapply IHuv2; apply rt_refl
                  | eapply IHuv3; apply rt_refl
                  ]
                end
              | pose proof t_trans _ _ _ _ _ STRICT1 STRICT2 as STRICT3;
                eapply uvalue_strict_subterm_inv in STRICT3 as (s&DIRECT&SUB);
                inv DIRECT;
                [ eapply IHuv1; eauto
                | eapply IHuv2; eauto
                | eapply IHuv3; eauto
                ]
              ]
            | (* rt_trans *)
              match goal with
              | XY : clos_refl_trans uvalue uvalue_direct_subterm ?x ?y,
                  YZ : clos_refl_trans uvalue uvalue_direct_subterm ?y ?z,
                    IHuv1 : forall s : uvalue, uvalue_subterm s ?uv1 -> P s,
                IHuv2 : forall s : uvalue, uvalue_subterm s ?uv2 -> P s,
                IHuv3 : forall s : uvalue, uvalue_subterm s ?uv3 -> P s
                |- _ =>
                  pose proof rt_trans _ _ _ _ _ XY YZ as XZ;
                  apply clos_rt_inv in XZ as [EQ | [w [R TRANS]]];
                  [ subst;
                    pose proof uvalue_subterm_antisymmetric XY YZ; subst; eauto
                  | inv R;
                    [ eapply IHuv1; eauto
                    | eapply IHuv2; eauto
                    | eapply IHuv3; eauto
                    ]
                  ]
              end
            ]
          | (* Solve binops *)
            intros s H';
            dependent induction H';
            [ (* rt_step *)
              match goal with
              | H: uvalue_direct_subterm ?x _,
                  IHuv1 : forall s : uvalue, uvalue_subterm s ?uv1 -> P s,
                IHuv2 : forall s : uvalue, uvalue_subterm s ?uv2 -> P s
                                      |- P ?x =>
                inv H;
                apply IH_Subterm; eauto;
                [ intros; eapply IHuv1; eauto;
                  apply clos_t_rt; eauto
                | intros; eapply IHuv2; eauto;
                  apply clos_t_rt; eauto
                ]
              end
            | (* rt_refl *)
              eapply IH_Subterm;
              intros * STRICT;
              dependent induction STRICT;
              [ (* t_step *)
                match goal with
                | H: uvalue_direct_subterm ?x _,
                    IHuv1 : forall s : uvalue, uvalue_subterm s ?uv1 -> P s,
                  IHuv2 : forall s : uvalue, uvalue_subterm s ?uv2 -> P s
                                        |- P ?x =>
                  inv H;
                  [ eapply IHuv1; apply rt_refl
                  | eapply IHuv2; apply rt_refl
                  ]
                end
              | pose proof t_trans _ _ _ _ _ STRICT1 STRICT2 as STRICT3;
                eapply uvalue_strict_subterm_inv in STRICT3 as (s&DIRECT&SUB);
                inv DIRECT;
                [ eapply IHuv1; eauto
                | eapply IHuv2; eauto
                ]
              ]
            | (* rt_trans *)
              match goal with
              | XY : clos_refl_trans uvalue uvalue_direct_subterm ?x ?y,
                  YZ : clos_refl_trans uvalue uvalue_direct_subterm ?y ?z
                |- _ =>
                  pose proof rt_trans _ _ _ _ _ XY YZ as XZ;
                  apply clos_rt_inv in XZ as [EQ | [w [R TRANS]]];
                  [ subst;
                    pose proof uvalue_subterm_antisymmetric XY YZ; subst; eauto
                  | inv R;
                    [ eapply IHuv1; eauto
                    | eapply IHuv2; eauto
                    ]
                  ]
              end
            ]
          | (* Solve single subterm *)
            intros s H';
            dependent induction H';
            [ (* rt_step *)
              match goal with
              | H: uvalue_direct_subterm ?x _,
                  IHuv : forall s : uvalue, uvalue_subterm s ?uv1 -> P s
                                      |- P ?x =>
                inv H;
                apply IH_Subterm; eauto;
                intros; eapply IHuv; eauto;
                apply clos_t_rt; eauto
              end
            | (* rt_refl *)
              eapply IH_Subterm;
              intros * STRICT;
              dependent induction STRICT;
              [ (* t_step *)
                match goal with
                | H: uvalue_direct_subterm ?x _,
                    IHuv : forall s : uvalue, uvalue_subterm s ?uv1 -> P s
                                        |- P ?x =>
                  inv H;
                  eapply IHuv; apply rt_refl
                end
              | pose proof t_trans _ _ _ _ _ STRICT1 STRICT2 as STRICT3;
                eapply uvalue_strict_subterm_inv in STRICT3 as (s&DIRECT&SUB);
                inv DIRECT;
                eapply IHuv; eauto
              ]
            | (* rt_trans *)
              match goal with
              | XY : clos_refl_trans uvalue uvalue_direct_subterm ?x ?y,
                  YZ : clos_refl_trans uvalue uvalue_direct_subterm ?y ?z,
                    IHuv : forall s : uvalue, uvalue_subterm s ?uv1 -> P s
                |- _ =>
                  pose proof rt_trans _ _ _ _ _ XY YZ as XZ;
                  apply clos_rt_inv in XZ as [EQ | [w [R TRANS]]];
                  [ subst;
                    pose proof uvalue_subterm_antisymmetric XY YZ; subst; eauto
                  | inv R;
                    eapply IHuv; eauto
                  ]
              end
            ]
          ].

      { intros s H'.
        dependent induction H'.
        - (* rt_step *)
          match goal with
          | H: uvalue_direct_subterm ?x _,
              IH : forall u : uvalue, In u _ -> forall s : uvalue, uvalue_subterm s u -> P s
                                                        |- P ?x =>
              inv H;
              apply IH_Subterm; eauto;
              intros; eapply IH; eauto;
              apply clos_t_rt; eauto
          end.
        - (* rt_refl *)
          apply IH_Subterm.
          intros * STRICT;
            dependent induction STRICT.
          + (* t_step *)
              match goal with
              | H: uvalue_direct_subterm ?x _,
                  IH : forall u : uvalue, In u _ -> forall s : uvalue, uvalue_subterm s u -> P s
                                                            |- P ?x =>
                  inv H;
                  eapply IH; eauto;
                  apply rt_refl
              end.
          + (* t_trans *)
            match goal with
            | IH : forall u : uvalue, In u ?fields -> forall s : uvalue, uvalue_subterm s u -> P s
                                                              |- P ?x =>
                clear IHSTRICT1;
                specialize (IHSTRICT2 t fields);
                repeat (forward IHSTRICT2; auto);
                pose proof t_trans _ _ _ _ _ STRICT1 STRICT2 as STRICT3;
                eapply uvalue_strict_subterm_inv in STRICT3 as (s&DIRECT&SUB);
                inv DIRECT;
                eapply IH; eauto
            end.
        - (* rt_trans *)
          match goal with
          | XY : clos_refl_trans uvalue uvalue_direct_subterm ?x ?y,
              YZ : clos_refl_trans uvalue uvalue_direct_subterm ?y ?z,
                IH : forall u : uvalue, In u _ -> forall s : uvalue, uvalue_subterm s u -> P s
                                                          |- _ =>
              pose proof rt_trans _ _ _ _ _ XY YZ as XZ;
              apply clos_rt_inv in XZ as [EQ | [w [R TRANS]]];
              [ subst;
                pose proof uvalue_subterm_antisymmetric XY YZ; subst; eauto
              | inv R; eapply IH; eauto
              ]
          end.
      }

      { intros s H'.
        dependent induction H'.
        - (* rt_step *)
          match goal with
          | H: uvalue_direct_subterm ?x _,
              IH : forall u : uvalue, In u _ -> forall s : uvalue, uvalue_subterm s u -> P s
                                                        |- P ?x =>
              inv H;
              apply IH_Subterm; eauto;
              intros; eapply IH; eauto;
              apply clos_t_rt; eauto
          end.
        - (* rt_refl *)
          apply IH_Subterm.
          intros * STRICT;
            dependent induction STRICT.
          + (* t_step *)
              match goal with
              | H: uvalue_direct_subterm ?x _,
                  IH : forall u : uvalue, In u _ -> forall s : uvalue, uvalue_subterm s u -> P s
                                                            |- P ?x =>
                  inv H;
                  eapply IH; eauto;
                  apply rt_refl
              end.
          + (* t_trans *)
            match goal with
            | IH : forall u : uvalue, In u ?fields -> forall s : uvalue, uvalue_subterm s u -> P s
                                                              |- P ?x =>
                clear IHSTRICT1;
                specialize (IHSTRICT2 t fields);
                repeat (forward IHSTRICT2; auto);
                pose proof t_trans _ _ _ _ _ STRICT1 STRICT2 as STRICT3;
                eapply uvalue_strict_subterm_inv in STRICT3 as (s&DIRECT&SUB);
                inv DIRECT;
                eapply IH; eauto
            end.
        - (* rt_trans *)
          match goal with
          | XY : clos_refl_trans uvalue uvalue_direct_subterm ?x ?y,
              YZ : clos_refl_trans uvalue uvalue_direct_subterm ?y ?z,
                IH : forall u : uvalue, In u _ -> forall s : uvalue, uvalue_subterm s u -> P s
                                                          |- _ =>
              pose proof rt_trans _ _ _ _ _ XY YZ as XZ;
              apply clos_rt_inv in XZ as [EQ | [w [R TRANS]]];
              [ subst;
                pose proof uvalue_subterm_antisymmetric XY YZ; subst; eauto
              | inv R; eapply IH; eauto
              ]
          end.
      }

      { (* GEP *)
        intros s H';
          dependent induction H'.
        - (* rt_step *)
          inv H0.
          + (* addr *)
            eapply IHuv; apply rt_refl.
          + (* idxs *)
            eapply H; eauto.
            apply rt_refl.
        - (* rt_refl *)
          apply IH_Subterm;
            intros * STRICT;
            dependent induction STRICT.
          + (* t_step *)
            inv H0.
            * (* addr *)
              eapply IHuv; apply rt_refl.
            * (* idxs *)
              eapply H; eauto.
              apply rt_refl.
          + (* t_trans *)
            pose proof t_trans _ _ _ _ _ STRICT1 STRICT2 as STRICT3;
              eapply uvalue_strict_subterm_inv in STRICT3 as (s&DIRECT&SUB);
              inv DIRECT.
            * eapply IHuv; eauto.
            * eapply H; eauto.
        - (* rt_trans *)
          pose proof rt_trans _ _ _ _ _ H'1 H'2 as XZ;
            apply clos_rt_inv in XZ as [EQ | [w [R TRANS]]];
            [ subst;
              pose proof uvalue_subterm_antisymmetric H'1 H'2; subst; eauto
            |
            ].

          inv R;
            [ eapply IHuv; eauto
            | eapply H; eauto
            ].
      }

      { (* ConcatBytes *)
        intros s H';
          dependent induction H'.
        - (* rt_step *)
          inv H0.
          eapply H; eauto; apply rt_refl.
        - (* rt_refl *)
          apply IH_Subterm;
            intros * STRICT;
            dependent induction STRICT.
          + (* t_step *)
            inv H0.
            eapply H; eauto.
            apply rt_refl.
          + (* t_trans *)
            pose proof t_trans _ _ _ _ _ STRICT1 STRICT2 as STRICT3;
              eapply uvalue_strict_subterm_inv in STRICT3 as (s&DIRECT&SUB);
              inv DIRECT.
            * eapply H; eauto.
        - (* rt_trans *)
          pose proof rt_trans _ _ _ _ _ H'1 H'2 as XZ;
            apply clos_rt_inv in XZ as [EQ | [w [R TRANS]]];
            [ subst;
              pose proof uvalue_subterm_antisymmetric H'1 H'2; subst; eauto
            |
            ].

          inv R;
            eapply H; eauto.
      }
    Qed.
  End UvalueStrongInd.

  Section UvalueRec.
    Variable P : uvalue -> Set.
    Hypothesis IH_Addr           : forall a, P (UVALUE_Addr a).
    Hypothesis IH_I              : forall sz x, P (@UVALUE_I sz x).
    Hypothesis IH_IPTR            : forall x, P (UVALUE_IPTR x).
    Hypothesis IH_Double         : forall x, P (UVALUE_Double x).
    Hypothesis IH_Float          : forall x, P (UVALUE_Float x).
    Hypothesis IH_Undef          : forall t, P (UVALUE_Undef t).
    Hypothesis IH_Poison         : forall t, P (UVALUE_Poison t).
    Hypothesis IH_Oom            : forall t, P (UVALUE_Oom t).
    Hypothesis IH_None           : P UVALUE_None.
    Hypothesis IH_Struct         : forall (fields: list uvalue), (forall u, InT u fields -> P u) -> P (UVALUE_Struct fields).
    Hypothesis IH_Packed_Struct  : forall (fields: list uvalue), (forall u, InT u fields -> P u) -> P (UVALUE_Packed_struct fields).
    Hypothesis IH_Array          : forall t (elts: list uvalue), (forall e, InT e elts -> P e) -> P (UVALUE_Array t elts).
    Hypothesis IH_Vector         : forall t (elts: list uvalue), (forall e, InT e elts -> P e) -> P (UVALUE_Vector t elts).
    Hypothesis IH_IBinop         : forall (iop:ibinop) (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_IBinop iop v1 v2).
    Hypothesis IH_ICmp           : forall (cmp:icmp)   (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_ICmp cmp v1 v2).
    Hypothesis IH_FBinop         : forall (fop:fbinop) (fm:list fast_math) (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_FBinop fop fm v1 v2).
    Hypothesis IH_FCmp           : forall (cmp:fcmp)   (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_FCmp cmp v1 v2).
    Hypothesis IH_Conversion     : forall (conv:conversion_type) (t_from:dtyp) (v:uvalue) (t_to:dtyp), P v -> P (UVALUE_Conversion conv t_from v t_to).
    Hypothesis IH_GetElementPtr  : forall (t:dtyp) (ptrval:uvalue) (idxs:list (uvalue)), P ptrval -> (forall idx, InT idx idxs -> P idx) -> P (UVALUE_GetElementPtr t ptrval idxs).
    Hypothesis IH_ExtractElement : forall (t:dtyp) (vec: uvalue) (idx: uvalue), P vec -> P idx -> P (UVALUE_ExtractElement t vec idx).
    Hypothesis IH_InsertElement  : forall (t:dtyp) (vec: uvalue) (elt:uvalue) (idx:uvalue), P vec -> P elt -> P idx -> P (UVALUE_InsertElement t vec elt idx).
    Hypothesis IH_ShuffleVector  : forall (t:dtyp) (vec1:uvalue) (vec2:uvalue) (idxmask:uvalue), P vec1 -> P vec2 -> P idxmask -> P (UVALUE_ShuffleVector t vec1 vec2 idxmask).
    Hypothesis IH_ExtractValue   : forall (t:dtyp) (vec:uvalue) (idxs:list LLVMAst.int_ast), P vec -> P (UVALUE_ExtractValue t vec idxs).
    Hypothesis IH_InsertValue    : forall (t:dtyp) (vec:uvalue) (et:dtyp) (elt:uvalue) (idxs:list LLVMAst.int_ast), P vec -> P elt -> P (UVALUE_InsertValue t vec et elt idxs).
    Hypothesis IH_Select         : forall (cnd:uvalue) (v1:uvalue) (v2:uvalue), P cnd -> P v1 -> P v2 -> P (UVALUE_Select cnd v1 v2).
    Hypothesis IH_ExtractByte : forall (uv : uvalue) (dt : dtyp) (idx : N) (sid : N), P uv -> P (UVALUE_ExtractByte uv dt idx sid).
    Hypothesis IH_ConcatBytes : forall (dt : dtyp) (uvs : list uvalue),
        (forall u, InT u uvs -> P u) ->
        P (UVALUE_ConcatBytes uvs dt).

    Lemma uvalue_rec : forall (uv:uvalue), P uv.
      fix IH 1.
      remember P as P0 in IH.
      destruct uv; auto; subst.
      - apply IH_Struct.
        { revert fields.
          fix IHfields 1. intros [|u fields']. intros. inversion X.
          intros u' [<-|Hin]. apply IH. eapply IHfields. apply Hin.
        }
      - apply IH_Packed_Struct.
        { revert fields.
          fix IHfields 1. intros [|u fields']. intros. inversion X.
          intros u' [<-|Hin]. apply IH. eapply IHfields. apply Hin.
        }
      - apply IH_Array.
        { revert elts.
          fix IHelts 1. intros [|u elts']. intros. inversion X.
          intros u' [<-|Hin]. apply IH. eapply IHelts. apply Hin.
        }
      - apply IH_Vector.
        { revert elts.
          fix IHelts 1. intros [|u elts']. intros. inversion X.
          intros u' [<-|Hin]. apply IH. eapply IHelts. apply Hin.
        }
      - apply IH_IBinop; auto.
      - apply IH_ICmp; auto.
      - apply IH_FBinop; auto.
      - apply IH_FCmp; auto.
      - apply IH_Conversion; auto.
      - apply IH_GetElementPtr. apply IH.
        { revert idxs.
          fix IHidxs 1. intros [|u idxs']. intros. inversion X.
          intros u' [<-|Hin]. apply IH. eapply IHidxs. apply Hin.
        }
      - apply IH_ExtractElement; auto.
      - apply IH_InsertElement; auto.
      - apply IH_ShuffleVector; auto.
      - apply IH_ExtractValue; auto.
      - apply IH_InsertValue; auto.
      - apply IH_Select; auto.
      - apply IH_ExtractByte; auto.
      - apply IH_ConcatBytes.
        { revert uvs.
          fix IHuvs 1. intros [|u uvs']. intros. inversion X.
          intros u' [<-|Hin]. apply IH. eapply IHuvs. apply Hin.
        }
    Qed.
  End UvalueRec.


  Section UvalueInd''.
    Variable P : uvalue -> Prop.
    Hypothesis IH_Addr           : forall a, P (UVALUE_Addr a).
    Hypothesis IH_I              : forall sz x, P (@UVALUE_I sz x).
    Hypothesis IH_IPTR            : forall x, P (UVALUE_IPTR x).
    Hypothesis IH_Double         : forall x, P (UVALUE_Double x).
    Hypothesis IH_Float          : forall x, P (UVALUE_Float x).

    (* Undef *)
    Hypothesis IH_Undef_Array    :
      forall sz t
        (IH: P (UVALUE_Undef t)),
        P (UVALUE_Undef (DTYPE_Array sz t)).

    Hypothesis IH_Undef_Vector    :
      forall sz t
        (IH: P (UVALUE_Undef t)),
        P (UVALUE_Undef (DTYPE_Vector sz t)).

    Hypothesis IH_Undef_Struct_nil    :
        P (UVALUE_Undef (DTYPE_Struct [])).

    Hypothesis IH_Undef_Struct_cons    : forall dt dts,
        P (UVALUE_Undef dt) ->
        P (UVALUE_Undef (DTYPE_Struct dts)) ->
        P (UVALUE_Undef (DTYPE_Struct (dt :: dts))).

    Hypothesis IH_Undef_Packed_struct_nil    :
        P (UVALUE_Undef (DTYPE_Packed_struct [])).

    Hypothesis IH_Undef_Packed_struct_cons    : forall dt dts,
        P (UVALUE_Undef dt) ->
        P (UVALUE_Undef (DTYPE_Packed_struct dts)) ->
        P (UVALUE_Undef (DTYPE_Packed_struct (dt :: dts))).

    Hypothesis IH_Undef          : forall t,
        ((forall dts, t <> DTYPE_Struct dts) /\ (forall dts, t <> DTYPE_Packed_struct dts) /\ (forall sz et, t <> DTYPE_Array sz et) /\ (forall sz et, t <> DTYPE_Vector sz et)) ->
        P (UVALUE_Undef t).

    (* Poison *)
    Hypothesis IH_Poison_Array    :
      forall sz t
        (IH: P (UVALUE_Poison t)),
        P (UVALUE_Poison (DTYPE_Array sz t)).

    Hypothesis IH_Poison_Vector    :
      forall sz t
        (IH: P (UVALUE_Poison t)),
        P (UVALUE_Poison (DTYPE_Vector sz t)).

    Hypothesis IH_Poison_Struct_nil    :
        P (UVALUE_Poison (DTYPE_Struct [])).

    Hypothesis IH_Poison_Struct_cons    : forall dt dts,
        P (UVALUE_Poison dt) ->
        P (UVALUE_Poison (DTYPE_Struct dts)) ->
        P (UVALUE_Poison (DTYPE_Struct (dt :: dts))).

    Hypothesis IH_Poison_Packed_struct_nil    :
        P (UVALUE_Poison (DTYPE_Packed_struct [])).

    Hypothesis IH_Poison_Packed_struct_cons    : forall dt dts,
        P (UVALUE_Poison dt) ->
        P (UVALUE_Poison (DTYPE_Packed_struct dts)) ->
        P (UVALUE_Poison (DTYPE_Packed_struct (dt :: dts))).

    Hypothesis IH_Poison          : forall t,
        ((forall dts, t <> DTYPE_Struct dts) /\ (forall dts, t <> DTYPE_Packed_struct dts) /\ (forall sz et, t <> DTYPE_Array sz et) /\ (forall sz et, t <> DTYPE_Vector sz et)) ->
        P (UVALUE_Poison t).

    (* Oom *)
    Hypothesis IH_Oom_Array    :
      forall sz t
        (IH: P (UVALUE_Oom t)),
        P (UVALUE_Oom (DTYPE_Array sz t)).

    Hypothesis IH_Oom_Vector    :
      forall sz t
        (IH: P (UVALUE_Oom t)),
        P (UVALUE_Oom (DTYPE_Vector sz t)).

    Hypothesis IH_Oom_Struct_nil    :
        P (UVALUE_Oom (DTYPE_Struct [])).

    Hypothesis IH_Oom_Struct_cons    : forall dt dts,
        P (UVALUE_Oom dt) ->
        P (UVALUE_Oom (DTYPE_Struct dts)) ->
        P (UVALUE_Oom (DTYPE_Struct (dt :: dts))).

    Hypothesis IH_Oom_Packed_struct_nil    :
        P (UVALUE_Oom (DTYPE_Packed_struct [])).

    Hypothesis IH_Oom_Packed_struct_cons    : forall dt dts,
        P (UVALUE_Oom dt) ->
        P (UVALUE_Oom (DTYPE_Packed_struct dts)) ->
        P (UVALUE_Oom (DTYPE_Packed_struct (dt :: dts))).

    Hypothesis IH_Oom          : forall t,
        ((forall dts, t <> DTYPE_Struct dts) /\ (forall dts, t <> DTYPE_Packed_struct dts) /\ (forall sz et, t <> DTYPE_Array sz et) /\ (forall sz et, t <> DTYPE_Vector sz et)) ->
        P (UVALUE_Oom t).

    Hypothesis IH_None           : P UVALUE_None.
    Hypothesis IH_Struct_nil     : P (UVALUE_Struct []).
    Hypothesis IH_Struct_cons    : forall uv uvs, P uv -> P (UVALUE_Struct uvs) -> P (UVALUE_Struct (uv :: uvs)).
    Hypothesis IH_Packed_struct_nil     : P (UVALUE_Packed_struct []).
    Hypothesis IH_Packed_struct_cons    : forall uv uvs, P uv -> P (UVALUE_Packed_struct uvs) -> P (UVALUE_Packed_struct (uv :: uvs)).
    Hypothesis IH_Array          : forall t (elts: list uvalue), (forall e, In e elts -> P e) -> P (UVALUE_Array t elts).
    Hypothesis IH_Vector         : forall t (elts: list uvalue), (forall e, In e elts -> P e) -> P (UVALUE_Vector t elts).
    Hypothesis IH_IBinop         : forall (iop:ibinop) (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_IBinop iop v1 v2).
    Hypothesis IH_ICmp           : forall (cmp:icmp)   (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_ICmp cmp v1 v2).
    Hypothesis IH_FBinop         : forall (fop:fbinop) (fm:list fast_math) (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_FBinop fop fm v1 v2).
    Hypothesis IH_FCmp           : forall (cmp:fcmp)   (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_FCmp cmp v1 v2).
    Hypothesis IH_Conversion     : forall (conv:conversion_type) (t_from:dtyp) (v:uvalue) (t_to:dtyp), P v -> P (UVALUE_Conversion conv t_from v t_to).
    Hypothesis IH_GetElementPtr  : forall (t:dtyp) (ptrval:uvalue) (idxs:list (uvalue)), P ptrval -> (forall idx, In idx idxs -> P idx) -> P (UVALUE_GetElementPtr t ptrval idxs).
    Hypothesis IH_ExtractElement : forall (t:dtyp) (vec: uvalue) (idx: uvalue), P vec -> P idx -> P (UVALUE_ExtractElement t vec idx).
    Hypothesis IH_InsertElement  : forall (t:dtyp) (vec: uvalue) (elt:uvalue) (idx:uvalue), P vec -> P elt -> P idx -> P (UVALUE_InsertElement t vec elt idx).
    Hypothesis IH_ShuffleVector  : forall (t:dtyp) (vec1:uvalue) (vec2:uvalue) (idxmask:uvalue), P vec1 -> P vec2 -> P idxmask -> P (UVALUE_ShuffleVector t vec1 vec2 idxmask).
    Hypothesis IH_ExtractValue   : forall (t:dtyp) (vec:uvalue) (idxs:list LLVMAst.int_ast), P vec -> P (UVALUE_ExtractValue t vec idxs).
    Hypothesis IH_InsertValue    : forall (t:dtyp) (vec:uvalue) (et:dtyp) (elt:uvalue) (idxs:list LLVMAst.int_ast), P vec -> P elt -> P (UVALUE_InsertValue t vec et elt idxs).
    Hypothesis IH_Select         : forall (cnd:uvalue) (v1:uvalue) (v2:uvalue), P cnd -> P v1 -> P v2 -> P (UVALUE_Select cnd v1 v2).
    Hypothesis IH_ExtractByte : forall (uv : uvalue) (dt : dtyp) (idx : N) (sid : N), P uv -> P (UVALUE_ExtractByte uv dt idx sid).
    Hypothesis IH_ConcatBytes : forall (dt : dtyp) (uvs : list uvalue),
        (forall u, In u uvs -> P u) ->
        P (UVALUE_ConcatBytes uvs dt).

    Lemma uvalue_ind'' : forall (uv:uvalue), P uv.
      fix IH 1.
      remember P as P0 in IH.
      destruct uv; auto; subst.
      - generalize dependent t.
        fix IHτ 1.
        intros τ.
        destruct τ eqn:Hτ; try contradiction;
          try solve [eapply IH_Undef;
                     repeat split; solve [intros * CONTRA; inversion CONTRA]].

        (* Undef Arrays *)
        { apply IH_Undef_Array.
          apply IHτ.
        }

        (* Undef Structs *)
        { clear Hτ.
          generalize dependent fields.
          induction fields.
          - apply IH_Undef_Struct_nil.
          - apply IH_Undef_Struct_cons.
            apply IHτ.
            apply IHfields.
        }

        (* Undef Packed structs *)
        { clear Hτ.
          generalize dependent fields.
          induction fields.
          - apply IH_Undef_Packed_struct_nil.
          - apply IH_Undef_Packed_struct_cons.
            apply IHτ.
            apply IHfields.
        }

        (* Undef Vectors *)
        { apply IH_Undef_Vector.
          apply IHτ.
        }
      - generalize dependent t.
        fix IHτ 1.
        intros τ.
        destruct τ eqn:Hτ; try contradiction;
          try solve [eapply IH_Poison;
                     repeat split; solve [intros * CONTRA; inversion CONTRA]].

        (* Poison Arrays *)
        { apply IH_Poison_Array.
          apply IHτ.
        }

        (* Poison Structs *)
        { clear Hτ.
          generalize dependent fields.
          induction fields.
          - apply IH_Poison_Struct_nil.
          - apply IH_Poison_Struct_cons.
            apply IHτ.
            apply IHfields.
        }

        (* Poison Packed structs *)
        { clear Hτ.
          generalize dependent fields.
          induction fields.
          - apply IH_Poison_Packed_struct_nil.
          - apply IH_Poison_Packed_struct_cons.
            apply IHτ.
            apply IHfields.
        }

        (* Poison Vectors *)
        { apply IH_Poison_Vector.
          apply IHτ.
        }

      - generalize dependent t.
        fix IHτ 1.
        intros τ.
        destruct τ eqn:Hτ; try contradiction;
          try solve [eapply IH_Oom;
                     repeat split; solve [intros * CONTRA; inversion CONTRA]].

        (* Oom Arrays *)
        { apply IH_Oom_Array.
          apply IHτ.
        }

        (* Oom Structs *)
        { clear Hτ.
          generalize dependent fields.
          induction fields.
          - apply IH_Oom_Struct_nil.
          - apply IH_Oom_Struct_cons.
            apply IHτ.
            apply IHfields.
        }

        (* Oom Packed structs *)
        { clear Hτ.
          generalize dependent fields.
          induction fields.
          - apply IH_Oom_Packed_struct_nil.
          - apply IH_Oom_Packed_struct_cons.
            apply IHτ.
            apply IHfields.
        }

        (* Oom Vectors *)
        { apply IH_Oom_Vector.
          apply IHτ.
        }

      - revert fields.
        fix IHfields 1. intros [|u' fields']. intros. apply IH_Struct_nil.
        apply IH_Struct_cons.
        apply IH.
        apply IHfields.
      - revert fields.
        fix IHfields 1. intros [|u' fields']. intros. apply IH_Packed_struct_nil.
        apply IH_Packed_struct_cons.
        apply IH.
        apply IHfields.
      - apply IH_Array.
        { revert elts.
          fix IHelts 1. intros [|u elts']. intros. inversion H.
          intros u' [<-|Hin]. apply IH. eapply IHelts. apply Hin.
        }
      - apply IH_Vector.
        { revert elts.
          fix IHelts 1. intros [|u elts']. intros. inversion H.
          intros u' [<-|Hin]. apply IH. eapply IHelts. apply Hin.
        }
      - apply IH_IBinop; auto.
      - apply IH_ICmp; auto.
      - apply IH_FBinop; auto.
      - apply IH_FCmp; auto.
      - apply IH_Conversion; auto.
      - apply IH_GetElementPtr. apply IH.
        { revert idxs.
          fix IHidxs 1. intros [|u idxs']. intros. inversion H.
          intros u' [<-|Hin]. apply IH. eapply IHidxs. apply Hin.
        }
      - apply IH_ExtractElement; auto.
      - apply IH_InsertElement; auto.
      - apply IH_ShuffleVector; auto.
      - apply IH_ExtractValue; auto.
      - apply IH_InsertValue; auto.
      - apply IH_Select; auto.
      - apply IH_ExtractByte; auto.
      - apply IH_ConcatBytes.
        { revert uvs.
          fix IHuvs 1. intros [|u uvs']. intros. inversion H.
          intros u' [<-|Hin]. apply IH. eapply IHuvs. apply Hin.
        }
    Qed.
  End UvalueInd''.

  Section UvalueRec''.
    Variable P : uvalue -> Set.
    Hypothesis IH_Addr           : forall a, P (UVALUE_Addr a).
    Hypothesis IH_I              : forall sz x, P (@UVALUE_I sz x).
    Hypothesis IH_IPTR            : forall x, P (UVALUE_IPTR x).
    Hypothesis IH_Double         : forall x, P (UVALUE_Double x).
    Hypothesis IH_Float          : forall x, P (UVALUE_Float x).

    (* Undef *)
    Hypothesis IH_Undef_Array    :
      forall sz t
        (IH: P (UVALUE_Undef t)),
        P (UVALUE_Undef (DTYPE_Array sz t)).

    Hypothesis IH_Undef_Vector    :
      forall sz t
        (IH: P (UVALUE_Undef t)),
        P (UVALUE_Undef (DTYPE_Vector sz t)).

    Hypothesis IH_Undef_Struct_nil    :
        P (UVALUE_Undef (DTYPE_Struct [])).

    Hypothesis IH_Undef_Struct_cons    : forall dt dts,
        P (UVALUE_Undef dt) ->
        P (UVALUE_Undef (DTYPE_Struct dts)) ->
        P (UVALUE_Undef (DTYPE_Struct (dt :: dts))).

    Hypothesis IH_Undef_Packed_struct_nil    :
        P (UVALUE_Undef (DTYPE_Packed_struct [])).

    Hypothesis IH_Undef_Packed_struct_cons    : forall dt dts,
        P (UVALUE_Undef dt) ->
        P (UVALUE_Undef (DTYPE_Packed_struct dts)) ->
        P (UVALUE_Undef (DTYPE_Packed_struct (dt :: dts))).

    Hypothesis IH_Undef          : forall t,
        ((forall dts, t <> DTYPE_Struct dts) /\ (forall dts, t <> DTYPE_Packed_struct dts) /\ (forall sz et, t <> DTYPE_Array sz et) /\ (forall sz et, t <> DTYPE_Vector sz et)) ->
        P (UVALUE_Undef t).

    (* Poison *)
    Hypothesis IH_Poison_Array    :
      forall sz t
        (IH: P (UVALUE_Poison t)),
        P (UVALUE_Poison (DTYPE_Array sz t)).

    Hypothesis IH_Poison_Vector    :
      forall sz t
        (IH: P (UVALUE_Poison t)),
        P (UVALUE_Poison (DTYPE_Vector sz t)).

    Hypothesis IH_Poison_Struct_nil    :
        P (UVALUE_Poison (DTYPE_Struct [])).

    Hypothesis IH_Poison_Struct_cons    : forall dt dts,
        P (UVALUE_Poison dt) ->
        P (UVALUE_Poison (DTYPE_Struct dts)) ->
        P (UVALUE_Poison (DTYPE_Struct (dt :: dts))).

    Hypothesis IH_Poison_Packed_struct_nil    :
        P (UVALUE_Poison (DTYPE_Packed_struct [])).

    Hypothesis IH_Poison_Packed_struct_cons    : forall dt dts,
        P (UVALUE_Poison dt) ->
        P (UVALUE_Poison (DTYPE_Packed_struct dts)) ->
        P (UVALUE_Poison (DTYPE_Packed_struct (dt :: dts))).

    Hypothesis IH_Poison          : forall t,
        ((forall dts, t <> DTYPE_Struct dts) /\ (forall dts, t <> DTYPE_Packed_struct dts) /\ (forall sz et, t <> DTYPE_Array sz et) /\ (forall sz et, t <> DTYPE_Vector sz et)) ->
        P (UVALUE_Poison t).

    (* Oom *)
    Hypothesis IH_Oom_Array    :
      forall sz t
        (IH: P (UVALUE_Oom t)),
        P (UVALUE_Oom (DTYPE_Array sz t)).

    Hypothesis IH_Oom_Vector    :
      forall sz t
        (IH: P (UVALUE_Oom t)),
        P (UVALUE_Oom (DTYPE_Vector sz t)).

    Hypothesis IH_Oom_Struct_nil    :
        P (UVALUE_Oom (DTYPE_Struct [])).

    Hypothesis IH_Oom_Struct_cons    : forall dt dts,
        P (UVALUE_Oom dt) ->
        P (UVALUE_Oom (DTYPE_Struct dts)) ->
        P (UVALUE_Oom (DTYPE_Struct (dt :: dts))).

    Hypothesis IH_Oom_Packed_struct_nil    :
        P (UVALUE_Oom (DTYPE_Packed_struct [])).

    Hypothesis IH_Oom_Packed_struct_cons    : forall dt dts,
        P (UVALUE_Oom dt) ->
        P (UVALUE_Oom (DTYPE_Packed_struct dts)) ->
        P (UVALUE_Oom (DTYPE_Packed_struct (dt :: dts))).

    Hypothesis IH_Oom          : forall t,
        ((forall dts, t <> DTYPE_Struct dts) /\ (forall dts, t <> DTYPE_Packed_struct dts) /\ (forall sz et, t <> DTYPE_Array sz et) /\ (forall sz et, t <> DTYPE_Vector sz et)) ->
        P (UVALUE_Oom t).

    Hypothesis IH_None           : P UVALUE_None.
    Hypothesis IH_Struct_nil     : P (UVALUE_Struct []).
    Hypothesis IH_Struct_cons    : forall uv uvs, P uv -> P (UVALUE_Struct uvs) -> P (UVALUE_Struct (uv :: uvs)).
    Hypothesis IH_Packed_struct_nil     : P (UVALUE_Packed_struct []).
    Hypothesis IH_Packed_struct_cons    : forall uv uvs, P uv -> P (UVALUE_Packed_struct uvs) -> P (UVALUE_Packed_struct (uv :: uvs)).
    Hypothesis IH_Array          : forall t (elts: list uvalue), (forall e, InT e elts -> P e) -> P (UVALUE_Array t elts).
    Hypothesis IH_Vector         : forall t (elts: list uvalue), (forall e, InT e elts -> P e) -> P (UVALUE_Vector t elts).
    Hypothesis IH_IBinop         : forall (iop:ibinop) (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_IBinop iop v1 v2).
    Hypothesis IH_ICmp           : forall (cmp:icmp)   (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_ICmp cmp v1 v2).
    Hypothesis IH_FBinop         : forall (fop:fbinop) (fm:list fast_math) (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_FBinop fop fm v1 v2).
    Hypothesis IH_FCmp           : forall (cmp:fcmp)   (v1:uvalue) (v2:uvalue), P v1 -> P v2 -> P (UVALUE_FCmp cmp v1 v2).
    Hypothesis IH_Conversion     : forall (conv:conversion_type) (t_from:dtyp) (v:uvalue) (t_to:dtyp), P v -> P (UVALUE_Conversion conv t_from v t_to).
    Hypothesis IH_GetElementPtr  : forall (t:dtyp) (ptrval:uvalue) (idxs:list (uvalue)), P ptrval -> (forall idx, InT idx idxs -> P idx) -> P (UVALUE_GetElementPtr t ptrval idxs).
    Hypothesis IH_ExtractElement : forall (t:dtyp) (vec: uvalue) (idx: uvalue), P vec -> P idx -> P (UVALUE_ExtractElement t vec idx).
    Hypothesis IH_InsertElement  : forall (t:dtyp) (vec: uvalue) (elt:uvalue) (idx:uvalue), P vec -> P elt -> P idx -> P (UVALUE_InsertElement t vec elt idx).
    Hypothesis IH_ShuffleVector  : forall (t:dtyp) (vec1:uvalue) (vec2:uvalue) (idxmask:uvalue), P vec1 -> P vec2 -> P idxmask -> P (UVALUE_ShuffleVector t vec1 vec2 idxmask).
    Hypothesis IH_ExtractValue   : forall (t:dtyp) (vec:uvalue) (idxs:list LLVMAst.int_ast), P vec -> P (UVALUE_ExtractValue t vec idxs).
    Hypothesis IH_InsertValue    : forall (t:dtyp) (vec:uvalue) (et:dtyp) (elt:uvalue) (idxs:list LLVMAst.int_ast), P vec -> P elt -> P (UVALUE_InsertValue t vec et elt idxs).
    Hypothesis IH_Select         : forall (cnd:uvalue) (v1:uvalue) (v2:uvalue), P cnd -> P v1 -> P v2 -> P (UVALUE_Select cnd v1 v2).
    Hypothesis IH_ExtractByte : forall (uv : uvalue) (dt : dtyp) (idx : N) (sid : N), P uv -> P (UVALUE_ExtractByte uv dt idx sid).
    Hypothesis IH_ConcatBytes : forall (dt : dtyp) (uvs : list uvalue),
        (forall u, InT u uvs -> P u) ->
        P (UVALUE_ConcatBytes uvs dt).

    Lemma uvalue_rec'' : forall (uv:uvalue), P uv.
      fix IH 1.
      remember P as P0 in IH.
      destruct uv; auto; subst.
      - generalize dependent t.
        fix IHτ 1.
        intros τ.
        destruct τ eqn:Hτ; try contradiction;
          try solve [eapply IH_Undef;
                     repeat split; solve [intros * CONTRA; inversion CONTRA]].

        (* Undef Arrays *)
        { apply IH_Undef_Array.
          apply IHτ.
        }

        (* Undef Structs *)
        { clear Hτ.
          generalize dependent fields.
          induction fields.
          - apply IH_Undef_Struct_nil.
          - apply IH_Undef_Struct_cons.
            apply IHτ.
            apply IHfields.
        }

        (* Undef Packed structs *)
        { clear Hτ.
          generalize dependent fields.
          induction fields.
          - apply IH_Undef_Packed_struct_nil.
          - apply IH_Undef_Packed_struct_cons.
            apply IHτ.
            apply IHfields.
        }

        (* Undef Vectors *)
        { apply IH_Undef_Vector.
          apply IHτ.
        }
      - generalize dependent t.
        fix IHτ 1.
        intros τ.
        destruct τ eqn:Hτ; try contradiction;
          try solve [eapply IH_Poison;
                     repeat split; solve [intros * CONTRA; inversion CONTRA]].

        (* Poison Arrays *)
        { apply IH_Poison_Array.
          apply IHτ.
        }

        (* Poison Structs *)
        { clear Hτ.
          generalize dependent fields.
          induction fields.
          - apply IH_Poison_Struct_nil.
          - apply IH_Poison_Struct_cons.
            apply IHτ.
            apply IHfields.
        }

        (* Poison Packed structs *)
        { clear Hτ.
          generalize dependent fields.
          induction fields.
          - apply IH_Poison_Packed_struct_nil.
          - apply IH_Poison_Packed_struct_cons.
            apply IHτ.
            apply IHfields.
        }

        (* Poison Vectors *)
        { apply IH_Poison_Vector.
          apply IHτ.
        }

      - generalize dependent t.
        fix IHτ 1.
        intros τ.
        destruct τ eqn:Hτ; try contradiction;
          try solve [eapply IH_Oom;
                     repeat split; solve [intros * CONTRA; inversion CONTRA]].

        (* Oom Arrays *)
        { apply IH_Oom_Array.
          apply IHτ.
        }

        (* Oom Structs *)
        { clear Hτ.
          generalize dependent fields.
          induction fields.
          - apply IH_Oom_Struct_nil.
          - apply IH_Oom_Struct_cons.
            apply IHτ.
            apply IHfields.
        }

        (* Oom Packed structs *)
        { clear Hτ.
          generalize dependent fields.
          induction fields.
          - apply IH_Oom_Packed_struct_nil.
          - apply IH_Oom_Packed_struct_cons.
            apply IHτ.
            apply IHfields.
        }

        (* Oom Vectors *)
        { apply IH_Oom_Vector.
          apply IHτ.
        }

      - revert fields.
        fix IHfields 1. intros [|u' fields']. intros. apply IH_Struct_nil.
        apply IH_Struct_cons.
        apply IH.
        apply IHfields.
      - revert fields.
        fix IHfields 1. intros [|u' fields']. intros. apply IH_Packed_struct_nil.
        apply IH_Packed_struct_cons.
        apply IH.
        apply IHfields.
      - apply IH_Array.
        { revert elts.
          fix IHelts 1. intros [|u elts']. intros. inversion X.
          intros u' [<-|Hin]. apply IH. eapply IHelts. apply Hin.
        }
      - apply IH_Vector.
        { revert elts.
          fix IHelts 1. intros [|u elts']. intros. inversion X.
          intros u' [<-|Hin]. apply IH. eapply IHelts. apply Hin.
        }
      - apply IH_IBinop; auto.
      - apply IH_ICmp; auto.
      - apply IH_FBinop; auto.
      - apply IH_FCmp; auto.
      - apply IH_Conversion; auto.
      - apply IH_GetElementPtr. apply IH.
        { revert idxs.
          fix IHidxs 1. intros [|u idxs']. intros. inversion X.
          intros u' [<-|Hin]. apply IH. eapply IHidxs. apply Hin.
        }
      - apply IH_ExtractElement; auto.
      - apply IH_InsertElement; auto.
      - apply IH_ShuffleVector; auto.
      - apply IH_ExtractValue; auto.
      - apply IH_InsertValue; auto.
      - apply IH_Select; auto.
      - apply IH_ExtractByte; auto.
      - apply IH_ConcatBytes.
        { revert uvs.
          fix IHuvs 1. intros [|u uvs']. intros. inversion X.
          intros u' [<-|Hin]. apply IH. eapply IHuvs. apply Hin.
        }
    Qed.
  End UvalueRec''.

  (* Injection of [dvalue] into [uvalue] *)
  Fixpoint dvalue_to_uvalue (dv : dvalue) : uvalue :=
    match dv with
    | DVALUE_Addr a => UVALUE_Addr a
    | @DVALUE_I sz x => @UVALUE_I sz x
    | DVALUE_IPTR x => UVALUE_IPTR x
    | DVALUE_Double x => UVALUE_Double x
    | DVALUE_Float x => UVALUE_Float x
    | DVALUE_Poison t => UVALUE_Poison t
    | DVALUE_Oom t => UVALUE_Oom t
    | DVALUE_None => UVALUE_None
    | DVALUE_Struct fields => UVALUE_Struct (map dvalue_to_uvalue fields)
    | DVALUE_Packed_struct fields => UVALUE_Packed_struct (map dvalue_to_uvalue fields)
    | DVALUE_Array t elts => UVALUE_Array t (map dvalue_to_uvalue elts)
    | DVALUE_Vector t elts => UVALUE_Vector t (map dvalue_to_uvalue elts)
    end.

  (* Partial injection of [uvalue] into [dvalue] *)
  Fixpoint uvalue_to_dvalue (uv : uvalue) : err dvalue :=
    match uv with
    | UVALUE_Addr a                          => ret (DVALUE_Addr a)
    | @UVALUE_I sz x                         => ret (@DVALUE_I sz x)
    | UVALUE_IPTR x                          => ret (DVALUE_IPTR x)
    | UVALUE_Double x                        => ret (DVALUE_Double x)
    | UVALUE_Float x                         => ret (DVALUE_Float x)
    | UVALUE_Undef t                         => failwith "Attempting to convert a non-defined uvalue to dvalue. The conversion should be guarded by is_concrete"
    | UVALUE_Poison t                        => ret (DVALUE_Poison t)
    | UVALUE_Oom t                           => ret (DVALUE_Oom t)
    | UVALUE_None                            => ret (DVALUE_None)

    | UVALUE_Struct fields                   =>
        fields' <- map_monad uvalue_to_dvalue fields ;;
        ret (DVALUE_Struct fields')

    | UVALUE_Packed_struct fields            =>
        fields' <- map_monad uvalue_to_dvalue fields ;;
        ret (DVALUE_Packed_struct fields')

    | UVALUE_Array t elts                      =>
        elts' <- map_monad uvalue_to_dvalue elts ;;
        ret (DVALUE_Array t elts')

    | UVALUE_Vector t elts                     =>
        elts' <- map_monad uvalue_to_dvalue elts ;;
        ret (DVALUE_Vector t elts')

    | _ => failwith "Attempting to convert a partially non-reduced uvalue to dvalue. Should not happen"
    end.

  Lemma uvalue_to_dvalue_of_dvalue_to_uvalue :
    forall (d : dvalue),
      uvalue_to_dvalue (dvalue_to_uvalue d : uvalue) = inr d.
  Proof using.
    intros.
    induction d; auto.
    - cbn. induction fields. cbn. reflexivity.
      assert (forall u : dvalue,
                 In u fields ->
                 uvalue_to_dvalue (dvalue_to_uvalue u : uvalue) = inr u).
      intros. apply H. apply in_cons; auto. specialize (IHfields H0).
      clear H0. rewrite map_cons. rewrite list_cons_app.
      rewrite map_monad_app. cbn.
      destruct (map_monad uvalue_to_dvalue (map dvalue_to_uvalue fields)) eqn: EQ.
      + discriminate IHfields.
      + rewrite H. cbn. inversion IHfields. reflexivity.
        constructor; auto.
    - cbn. induction fields. cbn. reflexivity.
      assert (forall u : dvalue,
                 In u fields ->
                 uvalue_to_dvalue (dvalue_to_uvalue u : uvalue) = inr u).
      intros. apply H. apply in_cons; auto. specialize (IHfields H0).
      clear H0. rewrite map_cons. rewrite list_cons_app.
      rewrite map_monad_app. cbn.
      destruct (map_monad uvalue_to_dvalue (map dvalue_to_uvalue fields)) eqn: EQ.
      + discriminate IHfields.
      + rewrite H. cbn. inversion IHfields. reflexivity.
        constructor; auto.
    - cbn. induction elts. cbn. reflexivity.
      assert (forall u : dvalue,
                 In u elts ->
                 uvalue_to_dvalue (dvalue_to_uvalue u : uvalue) = inr u).
      intros. apply H. apply in_cons; auto. specialize (IHelts H0).
      clear H0. rewrite map_cons. rewrite list_cons_app.
      rewrite map_monad_app. cbn.
      destruct (map_monad uvalue_to_dvalue (map dvalue_to_uvalue elts)) eqn: EQ.
      + discriminate IHelts.
      + rewrite H. cbn. inversion IHelts. reflexivity.
        constructor; auto.
    - cbn. induction elts. cbn. reflexivity.
      assert (forall u : dvalue,
                 In u elts ->
                 uvalue_to_dvalue (dvalue_to_uvalue u : uvalue) = inr u).
      intros. apply H. apply in_cons; auto. specialize (IHelts H0).
      clear H0. rewrite map_cons. rewrite list_cons_app.
      rewrite map_monad_app. cbn.
      destruct (map_monad uvalue_to_dvalue (map dvalue_to_uvalue elts)) eqn: EQ.
      + discriminate IHelts.
      + rewrite H. cbn. inversion IHelts. reflexivity.
        constructor; auto.
  Qed.


  (* returns true iff the uvalue contains no occurrence of UVALUE_Undef. *)
  (* YZ: See my comment above. If I'm correct, then we should also fail on operators and hence have:
   is_concrete uv = true <-> uvalue_to_dvalue uv = Some v
   *)
  Fixpoint is_concrete (uv : uvalue) : bool :=
    match uv with
    | UVALUE_Addr a => true
    | UVALUE_I sz x => true
    | UVALUE_IPTR x => true
    | UVALUE_Double x => true
    | UVALUE_Float x => true
    | UVALUE_Undef t => false
    | UVALUE_Poison t => true
    | UVALUE_Oom t => true (* A little unsure about this *)
    | UVALUE_None => true
    | UVALUE_Struct fields => forallb is_concrete fields
    | UVALUE_Packed_struct fields => forallb is_concrete fields
    | UVALUE_Array t elts => forallb is_concrete elts
    | UVALUE_Vector t elts => forallb is_concrete elts
    | _ => false
    end.

  (* Check if a uvalue contains any instances of `undef` or `poison` *)
  Fixpoint contains_undef_or_poison (uv : uvalue) : bool :=
    match uv with
    | UVALUE_Struct fields
    | UVALUE_Packed_struct fields =>
        anyb contains_undef_or_poison fields
    | UVALUE_Array t elts
    | UVALUE_Vector t elts =>
        anyb contains_undef_or_poison elts
    | UVALUE_IBinop iop v1 v2 =>
        contains_undef_or_poison v1 || contains_undef_or_poison v2
    | UVALUE_ICmp cmp v1 v2 =>
        contains_undef_or_poison v1 || contains_undef_or_poison v2
    | UVALUE_FBinop fop fm v1 v2 =>
        contains_undef_or_poison v1 || contains_undef_or_poison v2
    | UVALUE_FCmp cmp v1 v2 =>
        contains_undef_or_poison v1 || contains_undef_or_poison v2
    | UVALUE_Conversion conv t_from v t_to =>
        contains_undef_or_poison v
    | UVALUE_GetElementPtr t ptrval idxs =>
        contains_undef_or_poison ptrval || anyb contains_undef_or_poison idxs
    | UVALUE_ExtractElement vec_typ vec idx =>
        contains_undef_or_poison vec || contains_undef_or_poison idx
    | UVALUE_InsertElement vec_typ vec elt idx =>
        contains_undef_or_poison vec || contains_undef_or_poison elt || contains_undef_or_poison idx
    | UVALUE_ShuffleVector vec_typ vec1 vec2 idxmask =>
        contains_undef_or_poison vec1 || contains_undef_or_poison vec2 || contains_undef_or_poison idxmask
    | UVALUE_ExtractValue vec_typ vec idxs =>
        contains_undef_or_poison vec
    | UVALUE_InsertValue vec_typ vec elt_typ elt idxs =>
        contains_undef_or_poison vec || contains_undef_or_poison elt
    | UVALUE_Select cnd v1 v2 =>
        contains_undef_or_poison cnd || contains_undef_or_poison v1 || contains_undef_or_poison v2
    | UVALUE_ExtractByte uv dt idx sid =>
        contains_undef_or_poison uv
    | UVALUE_ConcatBytes uvs dt =>
        anyb contains_undef_or_poison uvs
    | UVALUE_Poison _
    | UVALUE_Undef _ =>
        true
    | _ =>
        false
    end.

  (* If both operands are concrete, uvalue_to_dvalue them and run them through
   opd, else run the abstract ones through opu *)
  Definition uvalue_to_dvalue_binop {A : Type}
             (opu : uvalue -> uvalue -> A) (opd : dvalue -> dvalue -> A) (uv1 uv2 : uvalue) : A :=
    let ma := dv1 <- uvalue_to_dvalue uv1 ;; dv2 <- uvalue_to_dvalue uv2 ;; ret (opd dv1 dv2)
    in match ma with
       | inl e => opu uv1 uv2
       | inr a => a
       end.

  (* Like uvalue_to_dvalue_binop, but the second operand is already concrete *)
  Definition uvalue_to_dvalue_binop2 {A : Type}
             (opu : uvalue -> uvalue -> A) (opd : dvalue -> dvalue -> A) (uv1 : uvalue) (dv2 : dvalue) : A :=
    let ma := dv1 <- uvalue_to_dvalue uv1 ;; ret (opd dv1 dv2)
    in match ma with
       | inl e => opu uv1 (dvalue_to_uvalue dv2 : uvalue)
       | inr a => a
       end.

  Definition uvalue_to_dvalue_uop {A : Type}
             (opu : uvalue -> A) (opd : dvalue -> A) (uv : uvalue ) : A :=
    let ma := dv <- uvalue_to_dvalue uv ;; ret (opd dv)
    in match ma with
       | inl e => opu uv
       | inr a => a
       end.

  Lemma uvalue_to_dvalue_list :
    forall fields,
      (forall u : uvalue,
          List.In u fields ->
          is_concrete u = true -> exists dv : dvalue, uvalue_to_dvalue u = inr dv) ->
      forallb is_concrete fields = true ->
      exists dfields, map_monad uvalue_to_dvalue fields = inr dfields.
  Proof using.
    induction fields; intros H ALL.
    - exists nil. reflexivity.
    - assert (List.In a (a :: fields)) as IN by intuition auto with *.

      change (a :: fields) with ([a] ++ fields)%list in ALL.
      rewrite forallb_app in ALL.
      apply andb_prop in ALL as (CONC_A & CONC_FIELDS).

      cbn in CONC_A.
      rewrite Bool.andb_true_r in CONC_A.
      pose proof (H a IN CONC_A) as (dv & CONV_A).

      assert (forall u : uvalue,
                 List.In u fields -> is_concrete u = true -> exists dv : dvalue, uvalue_to_dvalue u = inr dv) as HCONV.
      { intros u INFS CONCU.
        apply H; intuition auto with *.
      }

      pose proof (IHfields HCONV CONC_FIELDS) as (dfields & CONV_DFIELDS).
      exists (dv :: dfields).

      change (a :: fields) with ([a] ++ fields)%list.
      rewrite map_monad_app.
      cbn.
      rewrite CONV_A.
      rewrite CONV_DFIELDS.
      reflexivity.
  Qed.

  Lemma is_concrete_uvalue_to_dvalue :
    forall uv,
      is_concrete uv = true ->
      exists dv, uvalue_to_dvalue uv = inr dv.
  Proof using.
    intros uv CONC.
    induction uv;
      inversion CONC; try (eexists; reflexivity).
    - cbn.
      pose proof uvalue_to_dvalue_list _ H H1 as (dv & MAP).
      exists (DVALUE_Struct dv). rewrite MAP.
      reflexivity.
    - cbn.
      pose proof uvalue_to_dvalue_list _ H H1 as (dv & MAP).
      exists (DVALUE_Packed_struct dv). rewrite MAP.
      reflexivity.
    - cbn.
      pose proof uvalue_to_dvalue_list _ H H1 as (dv & MAP).
      exists (DVALUE_Array t dv). rewrite MAP.
      reflexivity.
    - cbn.
      pose proof uvalue_to_dvalue_list _ H H1 as (dv & MAP).
      exists (DVALUE_Vector t dv). rewrite MAP.
      reflexivity.
  Qed.

  Lemma uvalue_to_dvalue_list_concrete :
    forall fields dfields,
      (forall u : uvalue,
          In u fields ->
          (exists dv : dvalue, uvalue_to_dvalue u = inr dv) -> is_concrete u = true) ->
      map_monad uvalue_to_dvalue fields = inr dfields ->
      forallb is_concrete fields = true.
  Proof using.
    induction fields; intros dfields H MAP; auto.
    cbn. apply andb_true_intro.
    split.
    - apply H.
      + apply in_eq.
      + inversion MAP.
        destruct (uvalue_to_dvalue a) eqn:Hdv; inversion H1.
        exists d. reflexivity.
    - inversion MAP.
      destruct (uvalue_to_dvalue a) eqn:Hdv; inversion H1.
      destruct (map_monad uvalue_to_dvalue fields) eqn:Hmap; inversion H2.
      assert (forall u : uvalue,
                 In u fields -> (exists dv : dvalue, uvalue_to_dvalue u = inr dv) -> is_concrete u = true) as BLAH.
      { intros u IN (dv & CONV).
        apply H.
        - cbn. auto.
        - exists dv. auto.
      }
      apply (IHfields l BLAH eq_refl).
  Qed.

  Lemma uvalue_to_dvalue_is_concrete :
    forall uv dv,
      uvalue_to_dvalue uv = inr dv ->
      is_concrete uv = true.
  Proof using.
    induction uv;
      intros dv CONV; cbn; inversion CONV; auto.
    - break_match; inversion H1.
      eapply uvalue_to_dvalue_list_concrete; eauto.
      intros u IN (dv' & CONV').
      eapply H; eauto.
    - break_match; inversion H1.
      eapply uvalue_to_dvalue_list_concrete; eauto.
      intros u IN (dv' & CONV').
      eapply H; eauto.
    - break_match; inversion H1.
      eapply uvalue_to_dvalue_list_concrete; eauto.
      intros u IN (dv' & CONV').
      eapply H; eauto.
    - break_match; inversion H1.
      eapply uvalue_to_dvalue_list_concrete; eauto.
      intros u IN (dv' & CONV').
      eapply H; eauto.
  Qed.

  Section hiding_notation.
    #[local] Open Scope sexp_scope.

    Fixpoint serialize_dvalue' (dv:dvalue): sexp :=
      match dv with
      | DVALUE_Addr a => Atom "address" (* TODO: insist that memory models can print addresses? *)
      | DVALUE_I sz x => Atom ("dvalue(i" ++ show (Zpos sz) ++ ")")%string
      | DVALUE_IPTR x => Atom "dvalue(iptr)"
      | DVALUE_Double x => Atom "dvalue(double)"
      | DVALUE_Float x => Atom "dvalue(float)"
      | DVALUE_Poison t => Atom "poison"
      | DVALUE_Oom t => Atom "oom"
      | DVALUE_None => Atom "none"
      | DVALUE_Struct fields
        => [Atom "{" ; to_sexp (List.map (fun x => [serialize_dvalue' x ; Atom ","]) fields) ; Atom "}"]
      | DVALUE_Packed_struct fields
        => [Atom "packed{" ; to_sexp (List.map (fun x => [serialize_dvalue' x ; Atom ","]) fields) ; Atom "}"]
      | DVALUE_Array t elts
        => [Atom "[" ; to_sexp (List.map (fun x => [serialize_dvalue' x ; Atom ","]) elts) ; Atom "]"]
      | DVALUE_Vector t elts
        => [Atom "<" ; to_sexp (List.map (fun x => [serialize_dvalue' x ; Atom  ","]) elts) ; Atom ">"]
      end.

    #[global] Instance serialize_dvalue : Serialize dvalue := serialize_dvalue'.

    Fixpoint serialize_uvalue' (pre post: string) (uv:uvalue): sexp :=
      match uv with
      | UVALUE_Addr a => Atom (pre ++ "address" ++ post)%string (* TODO: insist that memory models can print addresses? *)
      | UVALUE_I sz x => Atom (pre ++ "uvalue(i" ++ show (Zpos sz) ++")" ++ post)%string
      | UVALUE_Double x => Atom (pre ++ "uvalue(double)" ++ post)%string
      | UVALUE_Float x => Atom (pre ++ "uvalue(float)" ++ post)%string
      | UVALUE_Poison t => Atom (pre ++ "poison" ++ post)%string
      | UVALUE_None => Atom (pre ++ "none" ++ post)%string
      | UVALUE_Struct fields
        => [Atom "{" ; to_sexp (List.map (serialize_uvalue' "" ",") fields) ; Atom "}"]
      | UVALUE_Packed_struct fields
        => [Atom "packed{" ; to_sexp (List.map (serialize_uvalue' "" ",") fields) ; Atom "}"]
      | UVALUE_Array t elts
        => [Atom "[" ; to_sexp (List.map (serialize_uvalue' "" ",") elts) ; Atom "]"]
      | UVALUE_Vector t elts
        => [Atom "<" ; to_sexp (List.map (serialize_uvalue' "" ",") elts) ; Atom ">"]
      | UVALUE_Undef t => [Atom "undef(" ; to_sexp t ; Atom ")"]
      | UVALUE_IBinop iop v1 v2 => [serialize_uvalue' "(" "" v1; to_sexp iop ; serialize_uvalue' "" ")" v2]
      | UVALUE_ICmp cmp v1 v2 => [serialize_uvalue' "(" "" v1; to_sexp cmp; serialize_uvalue' "" ")" v2]
      | UVALUE_FBinop fop _ v1 v2 => [serialize_uvalue' "(" "" v1; to_sexp fop; serialize_uvalue' "" ")" v2]
      | UVALUE_FCmp cmp v1 v2 => [serialize_uvalue' "(" "" v1; to_sexp cmp; serialize_uvalue' "" ")" v2]
      | _ => Atom "TODO: show_uvalue"
      end.

    #[global] Instance serialize_uvalue : Serialize (uvalue) := serialize_uvalue' "" "".

  End hiding_notation.

  Ltac dec_dvalue :=
    match goal with
    | [ |- { ?X ?a = ?X ?b} + { ?X ?a <> ?X ?b} ] => idtac
    | [ |- { ?X ?a = ?Y ?b} + { ?X ?a <> ?Y ?b} ] => right; intros H; inversion H
    | [ |- { ?X = ?X } + { ?X <> ?X } ] => left; reflexivity
    | [ |- { ?X = ?Y } + { ?X <> ?Y } ] => right; intros H; inversion H
    end.


  Section DecidableEquality.

    Definition dvalue_int_eq_dec_helper
      (sz1 sz2 : positive) (x1 : @int sz1) (x2 : @int sz2) : {@DVALUE_I sz1 x1 = @DVALUE_I sz2 x2} + {@DVALUE_I sz1 x1 <> @DVALUE_I sz2 x2}.
      destruct (Pos.eq_dec sz1 sz2); subst.
      - destruct (Integers.eq_dec x1 x2); subst; auto.
        right.
        intros CONTRA; inv CONTRA. subst_existT.
        contradiction.
      - right.
        intros CONTRA; inv CONTRA. subst_existT.
        contradiction.
    Defined.

    Definition uvalue_int_eq_dec_helper
      (sz1 sz2 : positive) (x1 : @int sz1) (x2 : @int sz2) : {@UVALUE_I sz1 x1 = @UVALUE_I sz2 x2} + {@UVALUE_I sz1 x1 <> @UVALUE_I sz2 x2}.
      destruct (Pos.eq_dec sz1 sz2); subst.
      - destruct (Integers.eq_dec x1 x2); subst; auto.
        right.
        intros CONTRA; inv CONTRA. subst_existT.
        contradiction.
      - right.
        intros CONTRA; inv CONTRA. subst_existT.
        contradiction.
    Defined.

    Program Definition dvalue_int_cmp (d1 d2:dvalue) : bool :=
      match d1, d2 with
      | @DVALUE_I sz1 x1, @DVALUE_I sz2 x2 =>
          _
      | _, _ => false
      end.
    Next Obligation.
      destruct (Pos.eq_dec sz1 sz2); subst.
      apply (if Integers.eq_dec x1 x2 then true else false).
      apply false.
    Defined.

    Fixpoint dvalue_eqb (d1 d2:dvalue) : bool :=
      let lsteq := list_eqb (Build_RelDec eq dvalue_eqb) in
      match d1, d2 with
      | DVALUE_Addr a1, DVALUE_Addr a2 =>
          if A.eq_dec a1 a2 then true else false
      | @DVALUE_I sz1 x1, @DVALUE_I sz2 x2 =>
          dvalue_int_cmp d1 d2
      | DVALUE_Double x1, DVALUE_Double x2 =>
          if Float.eq_dec x1 x2 then true else false
      | DVALUE_Float x1, DVALUE_Float x2 =>
          if Float32.eq_dec x1 x2 then true else false
      | DVALUE_Poison t1, DVALUE_Poison t2 =>
          dtyp_eqb t1 t2
      | DVALUE_None, DVALUE_None => true
      | DVALUE_Struct f1, DVALUE_Struct f2 =>
          lsteq f1 f2
      | DVALUE_Packed_struct f1, DVALUE_Packed_struct f2 =>
          lsteq f1 f2
      | DVALUE_Array t1 f1, DVALUE_Array t2 f2 =>
          dtyp_eqb t1 t2 && lsteq f1 f2
      | DVALUE_Vector t1 f1, DVALUE_Vector t2 f2 =>
          dtyp_eqb t1 t2 && lsteq f1 f2
      | _, _ => false
      end.

    Lemma dvalue_eq_dec : forall (d1 d2:dvalue), {d1 = d2} + {d1 <> d2}.
      refine (fix f d1 d2 :=
                let lsteq_dec := list_eq_dec f in
                match d1 with
                | DVALUE_Addr a1 =>
                    match d2 with
                    | DVALUE_Addr a2 => _
                    | _ => _
                    end
                | DVALUE_I sz1 x1 =>
                    match d2 with
                    | DVALUE_I sz2 x2 => _
                    | _ => _
                    end
                | DVALUE_IPTR x1 =>
                    match d2 with
                    | DVALUE_IPTR x2 => _
                    | _ => _
                    end
                | DVALUE_Double x1 =>
                    match d2 with
                    | DVALUE_Double x2 => _
                    | _ => _
                    end
                | DVALUE_Float x1 =>
                    match d2 with
                    | DVALUE_Float x2 => _
                    | _ => _
                    end
                | DVALUE_Poison _ =>
                    match d2 with
                    | DVALUE_Poison _ => _
                    | _ => _
                    end
                | DVALUE_Oom _ =>
                    match d2 with
                    | DVALUE_Oom _ => _
                    | _ => _
                    end
                | DVALUE_None =>
                    match d2 with
                    | DVALUE_None => _
                    | _ => _
                    end
                | DVALUE_Struct f1 =>
                    match d2 with
                    | DVALUE_Struct f2 => _
                    | _ => _
                    end
                | DVALUE_Packed_struct f1 =>
                    match d2 with
                    | DVALUE_Packed_struct f2 => _
                    | _ => _
                    end
                | DVALUE_Array t1 f1 =>
                    match d2 with
                    | DVALUE_Array t2 f2 => _
                    | _ => _
                    end
                | DVALUE_Vector t1 f1 =>
                    match d2 with
                    | DVALUE_Vector t2 f2 => _
                    | _ => _
                    end
                end);  try solve[ltac:(dec_dvalue)].
      - destruct (A.eq_dec a1 a2).
        * left; subst; reflexivity.
        * right; intros H; inversion H. contradiction.
      - apply dvalue_int_eq_dec_helper.
      - destruct (IP.eq_dec x1 x2).
        * left; subst; reflexivity.
        * right; intros H; inversion H. contradiction.
      - destruct (Float.eq_dec x1 x2).
        * left; subst; reflexivity.
        * right; intros H; inversion H. contradiction.
      - destruct (Float32.eq_dec x1 x2).
        * left; subst; reflexivity.
        * right; intros H; inversion H. contradiction.
      - destruct (dtyp_eq_dec d d0).
        * left; subst; reflexivity.
        * right; intros H; inversion H. contradiction.
      - destruct (dtyp_eq_dec d d0).
        * left; subst; reflexivity.
        * right; intros H; inversion H. contradiction.
      - destruct (lsteq_dec f1 f2).
        * left; subst; reflexivity.
        * right; intros H; inversion H. contradiction.
      - destruct (lsteq_dec f1 f2).
        * left; subst; reflexivity.
        * right; intros H; inversion H. contradiction.
      - destruct (dtyp_eq_dec t1 t2); subst.
        + destruct (lsteq_dec f1 f2).
          * left; subst; reflexivity.
          * right; intros H; inversion H. contradiction.
        + right.
          intros CONTRA; inv CONTRA; contradiction.
      - destruct (dtyp_eq_dec t1 t2); subst.
        + destruct (lsteq_dec f1 f2).
          * left; subst; reflexivity.
          * right; intros H; inversion H. contradiction.
        + right.
          intros CONTRA; inv CONTRA; contradiction.
    Qed.

    #[global] Instance eq_dec_dvalue : RelDec (@eq dvalue) := RelDec_from_dec (@eq dvalue) (@dvalue_eq_dec).
    #[global] Instance eqv_dvalue : Eqv dvalue := (@eq dvalue).
    Hint Unfold eqv_dvalue : core.

    Lemma ibinop_eq_dec : forall (op1 op2:ibinop), {op1 = op2} + {op1 <> op2}.
      intros.
      repeat decide equality.
    Qed.

    Lemma fbinop_eq_dec : forall (op1 op2:fbinop), {op1 = op2} + {op1 <> op2}.
      intros.
      repeat decide equality.
    Qed.

    Lemma icmp_eq_dec : forall (op1 op2:icmp), {op1 = op2} + {op1 <> op2}.
      intros.
      repeat decide equality.
    Qed.

    Lemma fcmp_eq_dec : forall (op1 op2:fcmp), {op1 = op2} + {op1 <> op2}.
      intros.
      repeat decide equality.
    Qed.

    Lemma fast_math_eq_dec : forall (op1 op2:fast_math), {op1 = op2} + {op1 <> op2}.
      intros.
      repeat decide equality.
    Qed.

    Lemma conversion_type_eq_dec : forall (op1 op2:conversion_type), {op1 = op2} + {op1 <> op2}.
      intros.
      repeat decide equality.
    Qed.

    Arguments ibinop_eq_dec: clear implicits.
    Arguments fbinop_eq_dec: clear implicits.
    Arguments icmp_eq_dec: clear implicits.
    Arguments fcmp_eq_dec: clear implicits.
    Arguments fast_math_eq_dec: clear implicits.
    Arguments conversion_type_eq_dec: clear implicits.

    Ltac __abs := right; intros H; inversion H; contradiction.
    Ltac __eq := left; subst; reflexivity.

    Lemma uvalue_eq_dec : forall (u1 u2:uvalue), {u1 = u2} + {u1 <> u2}.
    Proof with (try (__eq || __abs)).
      refine (fix f u1 u2 :=
                let lsteq_dec := list_eq_dec f in
                match u1, u2 with
                | UVALUE_Addr a1, UVALUE_Addr a2 => _
                | @UVALUE_I sz1 x1, @UVALUE_I sz2 x2 => _
                | UVALUE_IPTR x1, UVALUE_IPTR x2 => _
                | UVALUE_Double x1, UVALUE_Double x2 => _
                | UVALUE_Float x1, UVALUE_Float x2 => _
                | UVALUE_Undef t1, UVALUE_Undef t2 => _
                | UVALUE_Poison t1, UVALUE_Poison t2 => _
                | UVALUE_Oom t1, UVALUE_Oom t2 => _
                | UVALUE_None, UVALUE_None => _
                | UVALUE_Struct f1, UVALUE_Struct f2 => _
                | UVALUE_Packed_struct f1, UVALUE_Packed_struct f2 => _
                | UVALUE_Array t1 f1, UVALUE_Array t2 f2 => _
                | UVALUE_Vector t1 f1, UVALUE_Vector t2 f2 => _
                | UVALUE_IBinop op uv1 uv2, UVALUE_IBinop op' uv1' uv2' => _
                | UVALUE_ICmp op uv1 uv2, UVALUE_ICmp op' uv1' uv2' => _
                | UVALUE_FBinop op fm uv1 uv2, UVALUE_FBinop op' fm' uv1' uv2' => _
                | UVALUE_FCmp op uv1 uv2, UVALUE_FCmp op' uv1' uv2' => _
                | UVALUE_Conversion ct tf u t, UVALUE_Conversion ct' tf' u' t' => _
                | UVALUE_GetElementPtr t u l, UVALUE_GetElementPtr t' u' l' => _
                | UVALUE_ExtractElement t u v, UVALUE_ExtractElement t' u' v' => _
                | UVALUE_InsertElement t u v x, UVALUE_InsertElement t' u' v' x' => _
                | UVALUE_ShuffleVector t u v x, UVALUE_ShuffleVector t' u' v' x' => _
                | UVALUE_ExtractValue t u l, UVALUE_ExtractValue t' u' l' => _
                | UVALUE_InsertValue t u et v l, UVALUE_InsertValue t' u' et' v' l' => _
                | UVALUE_Select u v w, UVALUE_Select u' v' w' => _
                | UVALUE_ExtractByte uv dt idx sid, UVALUE_ExtractByte uv' dt' idx' sid' => _
                | UVALUE_ConcatBytes uvs dt, UVALUE_ConcatBytes uvs' dt' => _
                | _, _ => _
                end); try solve [(ltac:(dec_dvalue); fail)].
      - destruct (A.eq_dec a1 a2)...
      - apply uvalue_int_eq_dec_helper.
      - destruct (IP.eq_dec x1 x2)...
      - destruct (Float.eq_dec x1 x2)...
      - destruct (Float32.eq_dec x1 x2)...
      - destruct (dtyp_eq_dec t1 t2)...
      - destruct (dtyp_eq_dec t1 t2)...
      - destruct (dtyp_eq_dec t1 t2)...
      - destruct (lsteq_dec f1 f2)...
      - destruct (lsteq_dec f1 f2)...
      - destruct (dtyp_eq_dec t1 t2); destruct (lsteq_dec f1 f2)...
      - destruct (dtyp_eq_dec t1 t2); destruct (lsteq_dec f1 f2)...
      - destruct (ibinop_eq_dec op op')...
        destruct (f uv1 uv1')...
        destruct (f uv2 uv2')...
      - destruct (icmp_eq_dec op op')...
        destruct (f uv1 uv1')...
        destruct (f uv2 uv2')...
      - destruct (fbinop_eq_dec op op')...
        destruct (list_eq_dec fast_math_eq_dec fm fm')...
        destruct (f uv1 uv1')...
        destruct (f uv2 uv2')...
      - destruct (fcmp_eq_dec op op')...
        destruct (f uv1 uv1')...
        destruct (f uv2 uv2')...
      - destruct (conversion_type_eq_dec ct ct')...
        destruct (f u u')...
        destruct (dtyp_eq_dec tf tf')...
        destruct (dtyp_eq_dec t t')...
      - destruct (dtyp_eq_dec t t')...
        destruct (f u u')...
        destruct (lsteq_dec l l')...
      - destruct (dtyp_eq_dec t t')...
        destruct (f u u')...
        destruct (f v v')...
      - destruct (dtyp_eq_dec t t')...
        destruct (f u u')...
        destruct (f v v')...
        destruct (f x x')...
      - destruct (f u u')...
        destruct (f v v')...
        destruct (f x x')...
        destruct (dtyp_eq_dec t t')...
      - destruct (dtyp_eq_dec t t')...
        destruct (f u u')...
        destruct (list_eq_dec Z.eq_dec l l')...
      - destruct (dtyp_eq_dec t t')...
        destruct (f u u')...
        destruct (dtyp_eq_dec et et')...
        destruct (f v v')...
        destruct (list_eq_dec Z.eq_dec l l')...
      - destruct (f u u')...
        destruct (f v v')...
        destruct (f w w')...
      - destruct (f uv uv')...
        destruct (N.eq_dec idx idx')...
        destruct (N.eq_dec sid sid')...
        destruct (dtyp_eq_dec dt dt')...
      - destruct (lsteq_dec uvs uvs')...
        destruct (dtyp_eq_dec dt dt')...
    Qed.

    #[global] Instance eq_dec_uvalue : RelDec (@eq uvalue) := RelDec_from_dec (@eq uvalue) (@uvalue_eq_dec).
    #[global] Instance eqv_uvalue : Eqv (uvalue) := (@eq uvalue).
    Hint Unfold eqv_uvalue : core.
    #[global] Instance eq_dec_uvalue_correct: @RelDec.RelDec_Correct uvalue (@Logic.eq uvalue) _ := _.

  End DecidableEquality.

  Definition is_DVALUE_I1 (d:dvalue) : bool :=
    match d with
    | @DVALUE_I 1 _ => true
    | _ => false
    end.

  Definition is_DVALUE_I8 (d:dvalue) : bool :=
    match d with
    | @DVALUE_I 8 _ => true
    | _ => false
    end.

  Definition is_DVALUE_I16 (d:dvalue) : bool :=
    match d with
    | @DVALUE_I 16 _ => true
    | _ => false
    end.

  Definition is_DVALUE_I32 (d:dvalue) : bool :=
    match d with
    | @DVALUE_I 32 _ => true
    | _ => false
    end.

  Definition is_DVALUE_I64 (d:dvalue) : bool :=
    match d with
    | @DVALUE_I 64 _ => true
    | _ => false
    end.

  Definition is_DVALUE_IX (d:dvalue) : bool :=
    match d with
    | @DVALUE_I _ _ => true
    | _ => false
    end.

  Class ToDvalue I : Type :=
    { to_dvalue : I -> dvalue;
    }.

  #[global] Instance VMemInt_intptr' : VMemInt intptr.
  apply VMemInt_intptr.
  Defined.

  #[global] Instance ToDvalue_intptr : ToDvalue intptr :=
    { to_dvalue := DVALUE_IPTR }.

  #[global] Instance ToDvalue_Int `{sz : positive} : ToDvalue (@int sz) :=
    { to_dvalue := @DVALUE_I sz }.

  (* Is a uvalue a concrete integer equal to i? *)
  Definition uvalue_int_eq_Z (uv : uvalue) (i : Z)
    := match uv with
       | @UVALUE_I sz x
         => Z.eqb (unsigned x) i
       | UVALUE_IPTR x => Z.eqb (IP.to_Z x) i
       | _ => false
       end.

  Definition dvalue_int_unsigned (dv : dvalue) : Z
    := match dv with
       | @DVALUE_I sz x => unsigned x
       | DVALUE_IPTR x => IP.to_unsigned x
       | _ => 0
       end.

  (* Check if this is an instruction which can trigger UB with division by 0. *)
  Definition iop_is_div (iop : ibinop) : bool :=
    match iop with
    | UDiv _ => true
    | SDiv _ => true
    | URem   => true
    | SRem   => true
    | _      => false
    end.

  Definition iop_is_signed (iop : ibinop) : bool :=
    match iop with
    | SDiv _ => true
    | SRem   => true
    | _      => false
    end.

  Definition iop_is_shift (iop : ibinop) : bool :=
    match iop with
    | Shl _ _ => true
    | LShr _ => true
    | AShr _ => true
    | _ => false
    end.

  (* Check if this is an instruction which can trigger UB with division by 0. *)
  Definition fop_is_div (fop : fbinop) : bool :=
    match fop with
    | FDiv => true
    | FRem => true
    | _    => false
    end.

  Definition undef_i1 : uvalue  := UVALUE_Undef (DTYPE_I 1).
  Definition undef_i8 : uvalue  := UVALUE_Undef (DTYPE_I 8).
  Definition undef_i16 : uvalue := UVALUE_Undef (DTYPE_I 16).
  Definition undef_i32 : uvalue := UVALUE_Undef (DTYPE_I 32).
  Definition undef_i64 : uvalue := UVALUE_Undef (DTYPE_I 64).
  Definition undef_int {Int} `{VInt Int} : uvalue  := UVALUE_Undef (DTYPE_I bitwidth).

  Definition to_uvalue {Int} `{ToDvalue Int} (i : Int) : uvalue := dvalue_to_uvalue (to_dvalue i).

  Section CONVERSIONS.

    (** ** Typed conversion
        Performs a dynamic conversion of a [dvalue] of type [t1] to one of type [t2].
        For instance, convert an integer over 8 bits to one over 1 bit by truncation.

        The conversion function is not pure, i.e. in particular cannot live in [DynamicValues.v]
        as would be natural, due to the [Int2Ptr] and [Ptr2Int] cases. At those types, the conversion
        needs to cast between integers and pointers, which depends on the memory model.
     *)

    (* Note: Inferring the subevent instance takes a small but non-trivial amount of time,
       and has to be done here hundreds and hundreds of times due to the brutal pattern matching on
       several values. Factoring the inference upfront is therefore necessary.
     *)

    (* A trick avoiding proofs that involve thousands of cases: we split the conversion into
      the composition of a huge case analysis that builds a value of [conv_case], and a function
      with only four cases to actually build the tree.
     *)
    Variant conv_case : Set :=
    | Conv_Pure    (x : dvalue)
    | Conv_ItoP    (x : dvalue)
    | Conv_PtoI    (x : dvalue)
    | Conv_Oom     (s: string)
    | Conv_Illegal (s: string).

    Variant ptr_conv_cases : Set :=
    | PtrConv_ItoP
    | PtrConv_PtoI
    | PtrConv_Neither.

    Definition get_conv_case_ptr conv (t1 : dtyp) (t2 : dtyp) : ptr_conv_cases
      := match conv with
         | Inttoptr =>
           match t1, t2 with
           | DTYPE_I 64, DTYPE_Pointer => PtrConv_ItoP
           | DTYPE_IPTR, DTYPE_Pointer => PtrConv_ItoP
           | _, _ => PtrConv_Neither
           end
         | Ptrtoint =>
           match t1, t2 with
           | DTYPE_Pointer, DTYPE_I _ => PtrConv_PtoI
           | DTYPE_Pointer, DTYPE_IPTR => PtrConv_PtoI
           | _, _ => PtrConv_Neither
           end
         | _ => PtrConv_Neither
         end.
  End CONVERSIONS.

  (* Arithmetic Operations ---------------------------------------------------- *)
  Section ARITHMETIC.

    (* Evaluate integer opererations to get a dvalue.

     These operations are between VInts, which are "vellvm"
     integers. This is a typeclass that wraps all of the integer
     operations that we use for integer types with different bitwidths.

     *)

    Definition to_dvalue_OOM {Int} `{ToDvalue Int} {M} `{Monad M} `{RAISE_OOM M}
               (i : OOM Int) : M dvalue
      := res <- lift_OOM i;;
         ret (to_dvalue res).

    Definition option_pred {A} (pred : A -> bool) (ma : option A) : bool
      := match ma with
         | Some x => pred x
         | None => false
         end.

    Definition eval_int_op {M} {Int} `{Monad M} `{RAISE_UB M} `{RAISE_ERROR M} `{RAISE_OOM M} `{VMemInt Int} `{ToDvalue Int} (iop:ibinop) (x y: Int) : M dvalue :=
      match iop with
      (* Following to cases are probably right since they use CompCert *)
      | Add nuw nsw =>
          if orb (andb nuw (mequ (madd_carry x y mzero) mone))
               (andb nsw (mequ (madd_overflow x y mzero) mone))
          then ret (DVALUE_Poison mdtyp_of_int)
          else to_dvalue_OOM (madd x y)

      | Sub nuw nsw =>
          if orb (andb nuw (mequ (msub_borrow x y mzero) mone))
               (andb nsw (mequ (msub_overflow x y mzero) mone))
          then ret (DVALUE_Poison mdtyp_of_int)
          else to_dvalue_OOM (msub x y)

      | Mul nuw nsw =>
          (* I1 mul can't overflow, just based on the 4 possible multiplications. *)
          if (option_pred (fun bw => Pos.eqb bw 1) mbitwidth)
          then to_dvalue_OOM (mmul x y)
          else
            res <- lift_OOM (mmul x y);;

            let res_u' := ((munsigned x) * (munsigned y))%Z in
            let res_s' := ((msigned x) * (msigned y))%Z in

            let min_s_bound := match fmap (fun m => m >? res_s') mmin_signed with
                               | None => false
                               | Some x => x
                               end in
            let max_s_bound := match fmap (fun m => res_s' >? m) mmax_signed with
                               | None => false
                               | Some x => x
                               end in

            if dtyp_eqb mdtyp_of_int DTYPE_IPTR
            then
              if (res_u' >? munsigned res)
              then raise_oom "Multiplication overflow on iptr."
              else ret (to_dvalue res)
            else
              if orb (andb nuw (res_u' >? munsigned res))
                   (andb nsw (orb min_s_bound max_s_bound))
              then ret (DVALUE_Poison mdtyp_of_int)
              else ret (to_dvalue res)

      | Shl nuw nsw =>
          res <- lift_OOM (mshl x y);;
          let res_u := munsigned res in
          let res_u' := Z.shiftl (munsigned x) (munsigned y) in

          if dtyp_eqb (@mdtyp_of_int Int _) DTYPE_IPTR
          then
            (* TODO: Do we need to check for the unsigned case? Return result anyway? *)
            if (res_u' >? res_u)
            then raise_oom "Shl unsigned overflow on iptr."
            else
              ret (to_dvalue res)
          else
            (* Unsigned shift x right by bitwidth - y. If shifted x != sign bit * (2^y - 1),
         then there is overflow. *)
            if option_pred (fun bw => munsigned y >=? Zpos bw) mbitwidth
            then ret (DVALUE_Poison mdtyp_of_int)
            else
              if andb nuw (res_u' >? res_u)
              then ret (DVALUE_Poison mdtyp_of_int)
              else
                (* Need to separate this out because mnegative can OOM *)
                if nsw
                then
                  match mbitwidth with
                  | None =>
                      ret (to_dvalue res)
                  | Some bw =>
                      (* TODO: should this OOM here? *)
                      nres <- lift_OOM (mnegative res);;
                      if (negb (Z.shiftr (munsigned x)
                                  (Zpos bw - munsigned y)
                                =? (munsigned nres)
                                   * (Z.pow 2 (munsigned y) - 1))%Z)
                      then ret (DVALUE_Poison mdtyp_of_int)
                      else ret (to_dvalue res)
                  end
                else ret (to_dvalue res)

      | UDiv ex =>
          if (munsigned y =? 0)%Z
          then raise_ub "Unsigned division by 0."
          else if andb ex (negb ((munsigned x) mod (munsigned y) =? 0))%Z
               then ret (DVALUE_Poison mdtyp_of_int)
               else ret (to_dvalue (mdivu x y))

      | SDiv ex =>
          if dtyp_eqb mdtyp_of_int DTYPE_IPTR
          then raise_error "Signed division for iptr."
          else
            (* What does signed i1 mean? *)
            if (msigned y =? 0)%Z
            then raise_ub "Signed division by 0."
            else if andb ex (negb ((msigned x) mod (msigned y) =? 0))%Z
                 then ret (DVALUE_Poison mdtyp_of_int)
                 else to_dvalue_OOM (mdivs x y)

      | LShr ex =>
          if option_pred (fun bw => (munsigned y) >=? Zpos bw) mbitwidth && negb (dtyp_eqb mdtyp_of_int DTYPE_IPTR)
          then ret (DVALUE_Poison mdtyp_of_int)
          else if andb ex (negb ((munsigned x)
                                   mod (Z.pow 2 (munsigned y)) =? 0))%Z
               then ret (DVALUE_Poison mdtyp_of_int) else ret (to_dvalue (mshru x y))

      | AShr ex =>
          if dtyp_eqb mdtyp_of_int DTYPE_IPTR
          then raise_error "Arithmetic shift for iptr."
          else
            if option_pred (fun bw => (munsigned y) >=? Zpos bw) mbitwidth
            then ret (DVALUE_Poison mdtyp_of_int)
            else if andb ex (negb ((munsigned x)
                                     mod (Z.pow 2 (munsigned y)) =? 0))%Z
                 then ret (DVALUE_Poison mdtyp_of_int) else ret (to_dvalue (mshr x y))

      | URem =>
          if (munsigned y =? 0)%Z
          then raise_ub "Unsigned mod 0."
          else ret (to_dvalue (mmodu x y))

      | SRem =>
          if dtyp_eqb mdtyp_of_int DTYPE_IPTR
          then raise_error "Signed division for iptr."
          else
            if (msigned y =? 0)%Z
            then raise_ub "Signed mod 0."
            else to_dvalue_OOM (mmods x y)
      | And =>
          ret (to_dvalue (mand x y))

      | Or =>
          ret (to_dvalue (mor x y))

      | Xor =>
          ret (to_dvalue (mxor x y))
      end.
    Arguments eval_int_op _ _ _ : simpl nomatch.

  (* Evaluate the given iop on the given arguments according to the bitsize *)
  Definition integer_op {M} `{HM : Monad M} `{ERR : RAISE_ERROR M} `{UB : RAISE_UB M} `{OOM : RAISE_OOM M} (bits:positive) (iop:ibinop) (x y:@int bits) : M dvalue :=
    eval_int_op iop x y.
  Arguments integer_op _ _ _ _ : simpl nomatch.

  (* Convert written integer constant to corresponding integer with bitsize bits.
     Takes the integer modulo 2^bits. *)
  Definition coerce_integer_to_int {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_UB M} `{RAISE_OOM M} (bits:option positive) (i:Z) : M dvalue :=
    match bits with
    | Some sz  => ret (@DVALUE_I sz (repr i))
    | None    =>
        i' <- lift_OOM (mrepr i);;
        ret (DVALUE_IPTR i')
    end.
  Arguments coerce_integer_to_int _ _ : simpl nomatch.

  (* Helper for looping 2 argument evaluation over vectors, producing a vector *)

  Definition vec_loop {A : Type} {M : Type -> Type} `{Monad M}
             (f : A -> A -> M A)
             (elts : list (A * A)) : M (list A) :=
    monad_fold_right (fun acc '(e1, e2) =>
                        val <- f e1 e2 ;;
                        ret (val :: acc)
                     ) elts [].


  (* Integer iop evaluation, called from eval_iop.
     Here the values must be integers. Helper defined
     in order to prevent eval_iop from being recursive. *)
  Definition eval_iop_integer_h {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_UB M} `{RAISE_OOM M} (iop : ibinop) (v1 v2 : dvalue) : M dvalue.
    refine
      (match v1, v2 with
       | @DVALUE_I sz1 i1, @DVALUE_I sz2 i2 =>
           _
       | DVALUE_IPTR i1, DVALUE_IPTR i2 =>
           eval_int_op iop i1 i2
       | DVALUE_Poison t, _             =>
           ret (DVALUE_Poison t)
       | _, DVALUE_Poison t             =>
           if iop_is_div iop
           then raise_ub "Division by poison."
           else ret (DVALUE_Poison t)
       | _, _                           => raise_error "ill_typed-iop"
       end).
    destruct (Pos.eq_dec sz1 sz2); subst.
    - apply (eval_int_op iop i1 i2).
    - apply (raise_error "ill_typed-iop: integer bitwidth mismatch.").
  Defined.

  (* I split the definition between the vector and other evaluations because
     otherwise eval_iop should be recursive to allow for vector calculations,
     but coq can't find a fixpoint. *)
  (* Here is where we want to add the case distinction  for uvalues

       - this should check for "determined" uvalues and then use eval_iop_integer_h
         otherwise leave the op symbolic

       - this should use the inclusion of dvalue into uvalue in the case that
         eval_iop_integer_h is calle

   *)

  Definition eval_iop {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_UB M} `{RAISE_OOM M} iop v1 v2 : M dvalue :=
    match v1, v2 with
    | (DVALUE_Vector t elts1), (DVALUE_Vector _ elts2) =>
      val <- vec_loop (eval_iop_integer_h iop) (List.combine elts1 elts2) ;;
      ret (DVALUE_Vector t val)
    | _, _ => eval_iop_integer_h iop v1 v2
    end.
  Arguments eval_iop _ _ _ : simpl nomatch.

  Definition eval_int_icmp {M} `{Monad M} `{RAISE_ERROR M} {Int} `{VMI : VMemInt Int} icmp (x y : Int) : M dvalue :=
    c <- match icmp with
        | Eq => ret (mcmpu Ceq x y)
        | Ne => ret (mcmpu Cne x y)
        | Ugt => ret (mcmpu Cgt x y)
        | Uge => ret (mcmpu Cge x y)
        | Ult => ret (mcmpu Clt x y)
        | Ule => ret (mcmpu Cle x y)
        | Sgt =>
            if dtyp_eqb (@mdtyp_of_int Int VMI) DTYPE_IPTR
            then raise_error "Signed '>' comparison on iptr type."
            else ret (mcmp Cgt x y)
        | Sge =>
            if dtyp_eqb (@mdtyp_of_int Int VMI) DTYPE_IPTR
            then raise_error "Signed '>=' comparison on iptr type."
            else ret (mcmp Cge x y)
        | Slt =>
            if dtyp_eqb (@mdtyp_of_int Int VMI) DTYPE_IPTR
            then raise_error "Signed '<' comparison on iptr type."
            else ret (mcmp Clt x y)
        | Sle =>
            if dtyp_eqb (@mdtyp_of_int Int VMI) DTYPE_IPTR
            then raise_error "Signed '>' comparison on iptr type."
            else ret (mcmp Cle x y)
        end;;
    ret (if c
         then @DVALUE_I 1 (Integers.one)
         else @DVALUE_I 1 (Integers.zero)).
  Arguments eval_int_icmp _ _ _ : simpl nomatch.

  Definition double_op {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_UB M} (fop:fbinop) (v1:ll_double) (v2:ll_double) : M dvalue :=
    match fop with
    | FAdd => ret (DVALUE_Double (b64_plus FT_Rounding v1 v2))
    | FSub => ret (DVALUE_Double (b64_minus FT_Rounding v1 v2))
    | FMul => ret (DVALUE_Double (b64_mult FT_Rounding v1 v2))
    | FDiv => ret (DVALUE_Double (b64_div FT_Rounding v1 v2))
    | FRem => raise_error "unimplemented double operation"
    end.

  Definition float_op {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_UB M} (fop:fbinop) (v1:ll_float) (v2:ll_float) : M dvalue :=
    match fop with
    | FAdd => ret (DVALUE_Float (b32_plus FT_Rounding v1 v2))
    | FSub => ret (DVALUE_Float (b32_minus FT_Rounding v1 v2))
    | FMul => ret (DVALUE_Float (b32_mult FT_Rounding v1 v2))
    | FDiv => ret (DVALUE_Float (b32_div FT_Rounding v1 v2))
    | FRem => raise_error "unimplemented float operation"
    end.

  Definition eval_fop {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_UB M} (fop:fbinop) (v1:dvalue) (v2:dvalue) : M dvalue :=
    match v1, v2 with
    | DVALUE_Float f1, DVALUE_Float f2   => float_op fop f1 f2
    | DVALUE_Double d1, DVALUE_Double d2 => double_op fop d1 d2
    | DVALUE_Poison t, _                 => ret (DVALUE_Poison t)
    | DVALUE_Float _, DVALUE_Poison t
    | DVALUE_Double _, DVALUE_Poison t
      =>
        if fop_is_div fop
        then raise_ub "Division by poison."
        else ret (DVALUE_Poison t)
    | _, _                               =>
        raise_error ("ill_typed-fop: " ++
                       (to_string fop) ++
                       " " ++
                       (to_string v1) ++
                       " " ++
                       (to_string v2))
    end.

  Definition not_nan32 (f:ll_float) : bool :=
    negb (Flocq.IEEE754.Binary.is_nan _ _ f).

  Definition ordered32 (f1 f2:ll_float) : bool :=
    andb (not_nan32 f1) (not_nan32 f2).

  Definition not_nan64 (f:ll_double) : bool :=
    negb (Flocq.IEEE754.Binary.is_nan _ _ f).

  Definition ordered64 (f1 f2:ll_double) : bool :=
    andb (not_nan64 f1) (not_nan64 f2).

  Definition float_cmp (fcmp:fcmp) (x:ll_float) (y:ll_float) : dvalue :=
    if match fcmp with
       | FFalse => false
       | FOeq => andb (ordered32 x y) (Float32.cmp Ceq x y)
       | FOgt => andb (ordered32 x y) (Float32.cmp Cgt x y)
       | FOge => andb (ordered32 x y) (Float32.cmp Cge x y)
       | FOlt => andb (ordered32 x y) (Float32.cmp Clt x y)
       | FOle => andb (ordered32 x y) (Float32.cmp Cle x y)
       | FOne => andb (ordered32 x y) (Float32.cmp Cne x y)
       | FOrd => ordered32 x y
       | FUno => negb (ordered32 x y)
       | FUeq => (Float32.cmp Ceq x y)
       | FUgt => (Float32.cmp Cgt x y)
       | FUge => (Float32.cmp Cge x y)
       | FUlt => (Float32.cmp Clt x y)
       | FUle => (Float32.cmp Cle x y)
       | FUne => (Float32.cmp Cne x y)
       | FTrue => true
       end
    then @DVALUE_I 1 Integers.one else @DVALUE_I 1 Integers.zero.
  Arguments float_cmp _ _ _ : simpl nomatch.

  Definition double_cmp (fcmp:fcmp) (x:ll_double) (y:ll_double) : dvalue :=
    if match fcmp with
       | FFalse => false
       | FOeq => andb (ordered64 x y) (Float.cmp Ceq x y)
       | FOgt => andb (ordered64 x y) (Float.cmp Cgt x y)
       | FOge => andb (ordered64 x y) (Float.cmp Cge x y)
       | FOlt => andb (ordered64 x y) (Float.cmp Clt x y)
       | FOle => andb (ordered64 x y) (Float.cmp Cle x y)
       | FOne => andb (ordered64 x y) (Float.cmp Cne x y)
       | FOrd => ordered64 x y
       | FUno => negb (ordered64 x y)
       | FUeq => (Float.cmp Ceq x y)
       | FUgt => (Float.cmp Cgt x y)
       | FUge => (Float.cmp Cge x y)
       | FUlt => (Float.cmp Clt x y)
       | FUle => (Float.cmp Cle x y)
       | FUne => (Float.cmp Cne x y)
       | FTrue => true
       end
    then @DVALUE_I 1 Integers.one else @DVALUE_I 1 Integers.zero.
    Arguments double_cmp _ _ _ : simpl nomatch.

  Definition eval_fcmp {M} `{Monad M} `{RAISE_ERROR M} (fcmp:fcmp) (v1:dvalue) (v2:dvalue) : M dvalue :=
    match v1, v2 with
    | DVALUE_Float f1, DVALUE_Float f2 => ret (float_cmp fcmp f1 f2)
    | DVALUE_Double f1, DVALUE_Double f2 => ret (double_cmp fcmp f1 f2)
    | DVALUE_Poison t1, DVALUE_Poison t2 => ret (DVALUE_Poison t1)
    | DVALUE_Poison t, DVALUE_Double _ => ret (DVALUE_Poison t)
    | DVALUE_Poison t, DVALUE_Float _ => ret (DVALUE_Poison t)
    | DVALUE_Double _, DVALUE_Poison t => ret (DVALUE_Poison t)
    | DVALUE_Float _, DVALUE_Poison t => ret (DVALUE_Poison t)
    | _, _ => raise_error "ill_typed-fcmp"
    end.

  End ARITHMETIC.

  (* Helper function for indexing into a structured datatype
     for extractvalue and insertvalue *)
  Definition index_into_str {M} `{Monad M} `{RAISE_ERROR M} (v:uvalue) (idx:LLVMAst.int_ast) : M uvalue :=
    let fix loop elts i :=
        match elts with
        | [] => raise_error "index_into_str: index out of bounds"
        | h :: tl =>
          if (i =? 0)%Z then ret h else loop tl (i-1)%Z
        end in
    match v with
    | UVALUE_Struct f => loop f idx
    | UVALUE_Packed_struct f => loop f idx
    | UVALUE_Array t e => loop e idx
    | _ => raise_error "index_into_str: invalid aggregate data"
    end.
  Arguments index_into_str _ _ : simpl nomatch.

  (* Helper function for indexing into a structured datatype
     for extractvalue and insertvalue *)
  Definition index_into_str_dv {M} `{Monad M} `{RAISE_ERROR M} (v:dvalue) (idx:LLVMAst.int_ast) : M dvalue :=
    let fix loop elts i :=
        match elts with
        | [] => raise_error "index_into_str_dv: index out of bounds"
        | h :: tl =>
          if (i =? 0)%Z then ret h else loop tl (i-1)%Z
        end in
    match v with
    | DVALUE_Struct f => loop f idx
    | DVALUE_Packed_struct f => loop f idx
    | DVALUE_Array t e => loop e idx
    | _ => raise_error "index_into_str_dv: invalid aggregate data"
    end.
  Arguments index_into_str_dv _ _ : simpl nomatch.

  (* Helper function for inserting into a structured datatype for insertvalue *)
  Definition insert_into_str {M} `{Monad M} `{RAISE_ERROR M} (str:dvalue) (v:dvalue) (idx:LLVMAst.int_ast) : M dvalue :=
    let fix loop (acc elts:list dvalue) (i:LLVMAst.int_ast) :=
        match elts with
        | [] => raise_error "insert_into_str: index out of bounds"
        | h :: tl =>
          (if i =? 0 then ret (acc ++ (v :: tl))
          else loop (acc ++ [h]) tl (i-1))%Z
        end%list in
    match str with
    | DVALUE_Struct f =>
      v <- (loop [] f idx) ;;
      ret (DVALUE_Struct v)

    | DVALUE_Packed_struct f =>
      v <- (loop [] f idx) ;;
      ret (DVALUE_Packed_struct v)

    | DVALUE_Array t e =>
      v <- (loop [] e idx) ;;
      ret (DVALUE_Array t v)

    | _ => raise_error "insert_into_str: invalid aggregate data"
    end.
  Arguments insert_into_str _ _ _ : simpl nomatch.

  Definition index_into_vec_dv {M} `{Monad M} `{RAISE_ERROR M} (elt_typ : dtyp) (v:dvalue) (idx:dvalue) : M dvalue.
    refine
      (let fix loop dt (elts : list dvalue) i :=
         match elts with
         | [] => ret (DVALUE_Poison dt) (* LangRef: if idx exceeds the length of val for a fixed-length vector, the result is a poison value *)
         | h :: tl =>
             if (i =? 0)%Z then ret h else loop dt tl (i-1)%Z
         end in
       match v with
       | DVALUE_Array t e
       | DVALUE_Vector t e =>
           match idx with
           | @DVALUE_I sz i2 =>
               (* TODO: should this be restricted to 32 / 64-bit integers? *)
               let iZ := signed i2 in
               match iZ with
               | Zneg _ =>
                   raise_error "index_into_vec_dv: negative index."
               | _ => loop elt_typ e iZ
               end
           | _ => raise_error "index_into_vec_dv: non-integer dvalue index."
           end
       | _ => raise_error "index_into_vec_dv: not a vector or array."
       end).
  Defined.
  Arguments index_into_vec_dv _ _ : simpl nomatch.

  Definition insert_into_vec_dv {M} `{Monad M} `{RAISE_ERROR M} (vec_typ : dtyp) (vec:dvalue) (v:dvalue) (idx:dvalue) : M dvalue :=
    let fix loop (acc elts:list dvalue) (i:LLVMAst.int_ast) :=
        match elts with
        | [] => None (* LangRef: if idx exceeds the length of val for a fixed-length vector, the result is a poison value *)
        | h :: tl =>
          (if i =? 0 then ret (acc ++ (v :: tl))
          else loop (acc ++ [h]) tl (i-1))%Z
        end%list in
    match vec with
    | DVALUE_Vector t e =>
        match idx with
        | @DVALUE_I _ i2 =>
            (* TODO: should this be restricted to 32 / 64-bit integers? *)
            let iZ := signed i2 in
            match iZ with
            | Zneg _ =>
                raise_error "insert_into_vec_dv: negative index"
            | _ =>
                match loop [] e iZ with
                | None =>
                    ret (DVALUE_Poison vec_typ)
                | Some elts =>
                    ret (DVALUE_Vector t elts)
                end
            end
        | _ =>
            raise_error "insert_into_vec_dv: non-integer dvalue index."
        end
    | DVALUE_Array t e =>
        match idx with
        | @DVALUE_I _ i2 =>
            (* TODO: should this be restricted to 32 / 64-bit integers? *)
            let iZ := signed i2 in
            match iZ with
            | Zneg _ =>
                raise_error "insert_into_vec_dv: negative index"
            | _ =>
                match loop [] e iZ with
                | None =>
                    ret (DVALUE_Poison vec_typ)
                | Some elts =>
                    ret (DVALUE_Array t elts)
                end
            end
        | _ =>
            raise_error "insert_into_vec_dv: non-integer dvalue index."
        end
    | _ => raise_error "insert_into_vec_dv: not a vector or array."
    end.
  Arguments insert_into_vec_dv _ _ _ : simpl nomatch.

(*  ------------------------------------------------------------------------- *)

  (* Interpretation of [uvalue] in terms of sets of [dvalue].
     Essentially used to implemenmt the handler for [pick], but also required to
     define some predicates passed as arguments to the [pick] events, hence why
     it's defined here.
   *)

  (* Poison not included because of concretize *)
  Unset Elimination Schemes.
  Inductive dvalue_has_dtyp : dvalue -> dtyp -> Prop :=
  | DVALUE_Addr_typ   : forall a, dvalue_has_dtyp (DVALUE_Addr a) DTYPE_Pointer
  | DVALUE_I_typ      : forall sz x, dvalue_has_dtyp (@DVALUE_I sz x) (DTYPE_I sz)
  | DVALUE_IPTR_typ   : forall x, dvalue_has_dtyp (DVALUE_IPTR x) DTYPE_IPTR
  | DVALUE_Double_typ : forall x, dvalue_has_dtyp (DVALUE_Double x) DTYPE_Double
  | DVALUE_Float_typ  : forall x, dvalue_has_dtyp (DVALUE_Float x) DTYPE_Float
  | DVALUE_None_typ   : dvalue_has_dtyp DVALUE_None DTYPE_Void
  | DVALUE_Poison_typ  : forall τ, NO_VOID τ -> dvalue_has_dtyp (DVALUE_Poison τ) τ
  | DVALUE_Oom_typ  : forall τ, NO_VOID τ -> dvalue_has_dtyp (DVALUE_Oom τ) τ

  | DVALUE_Struct_typ :
    forall fields dts,
      List.Forall2 dvalue_has_dtyp fields dts ->
      dvalue_has_dtyp (DVALUE_Struct fields) (DTYPE_Struct dts)

  | DVALUE_Packed_struct_typ :
    forall fields dts,
      List.Forall2 dvalue_has_dtyp fields dts ->
      dvalue_has_dtyp (DVALUE_Packed_struct fields) (DTYPE_Packed_struct dts)

  (* Do we have to exclude mmx? "There are no arrays, vectors or constants of this type" *)
  | DVALUE_Array_typ :
    forall xs sz dt,
      NO_VOID dt ->
      Forall (fun x => dvalue_has_dtyp x dt) xs ->
      length xs = (N.to_nat sz) ->
      dvalue_has_dtyp (DVALUE_Array (DTYPE_Array sz dt) xs) (DTYPE_Array sz dt)

  | DVALUE_Vector_typ :
      forall xs sz dt,
      NO_VOID dt ->
      Forall (fun x => dvalue_has_dtyp x dt) xs ->
      length xs = (N.to_nat sz) ->
      vector_dtyp dt ->
      dvalue_has_dtyp (DVALUE_Vector (DTYPE_Vector sz dt) xs) (DTYPE_Vector sz dt)
  .
  Set Elimination Schemes.

  #[global]
  Hint Constructors dvalue_has_dtyp : dvalue.

  Section dvalue_has_dtyp_ind.
    Variable P : dvalue -> dtyp -> Prop.
    Hypothesis IH_Addr           : forall a, P (DVALUE_Addr a) DTYPE_Pointer.
    Hypothesis IH_I              : forall sz x, P (@DVALUE_I sz x) (DTYPE_I sz).
    Hypothesis IH_IPTR           : forall x, P (DVALUE_IPTR x) DTYPE_IPTR.
    Hypothesis IH_Poison         : forall t (NV: NO_VOID t), P (DVALUE_Poison t) t.
    Hypothesis IH_Oom            : forall t (NV: NO_VOID t), P (DVALUE_Oom t) t.
    Hypothesis IH_Double         : forall x, P (DVALUE_Double x) DTYPE_Double.
    Hypothesis IH_Float          : forall x, P (DVALUE_Float x) DTYPE_Float.
    Hypothesis IH_None           : P DVALUE_None DTYPE_Void.

    Hypothesis IH_Struct :
      forall fields fts,
        List.Forall2 P fields fts ->
        P (DVALUE_Struct fields) (DTYPE_Struct fts).

    Hypothesis IH_Packed_struct :
      forall fields fts,
        List.Forall2 P fields fts ->
        P (DVALUE_Packed_struct fields) (DTYPE_Packed_struct fts).

    Hypothesis IH_Array : forall (xs : list dvalue)
                             sz
                            (dt : dtyp)
                            (IH : forall x, In x xs -> P x dt),
        NO_VOID dt ->
        Datatypes.length xs = (N.to_nat sz) ->
        P (DVALUE_Array (DTYPE_Array sz dt) xs) (DTYPE_Array sz dt).

    Hypothesis IH_Vector : forall (xs : list dvalue) sz (dt : dtyp)
                             (IH : forall x, In x xs -> P x dt),
        NO_VOID dt ->
        Datatypes.length xs = (N.to_nat sz) ->
        vector_dtyp dt -> P (DVALUE_Vector (DTYPE_Vector sz dt) xs) (DTYPE_Vector sz dt).

    Lemma dvalue_has_dtyp_ind : forall (dv:dvalue) (dt:dtyp) (TYP: dvalue_has_dtyp dv dt), P dv dt.
      fix IHQ 3.
      intros dv dt TYP.
      destruct TYP; eauto.

      - apply IH_Struct.
        revert fields dts H.
        fix IHL_A 3.
        intros fields dts H.
        destruct H.
        + constructor.
        + constructor.
          eauto.
          eauto.

      - apply IH_Packed_struct.
        revert fields dts H.
        fix IHL_A 3.
        intros fields dts H.
        destruct H.
        + constructor.
        + constructor.
          eauto.
          eauto.

      - apply IH_Array; auto.
        revert xs sz dt H H0 H1.
        fix IHL_C 5.
        intros xs sz dt HNV H EQ .
        destruct H.
        * intros x HIN. inversion HIN.
        * intros x' HIN. inversion HIN.
          -- rewrite <- H1.
             eapply IHQ.
             assumption.

          -- simpl in EQ.
             destruct (N.to_nat sz); inversion EQ.
             rewrite <- Nnat.Nat2N.id in H3.
             apply (IHL_C _ _ _ HNV H0 H3 x' H1).

      - apply IH_Vector; auto.
        revert xs sz dt H H0 H1 H2.
        fix IHL_C 5.
        intros xs sz dt HNV H EQ HX.
        destruct H.
        * intros x HIN. inversion HIN.
        * intros x' HIN. inversion HIN.
          -- rewrite <- H1.
             eapply IHQ.
             assumption.

          -- simpl in EQ.
             destruct (N.to_nat sz); inversion EQ.
             rewrite <- Nnat.Nat2N.id in H3.
             apply (IHL_C _ _ _ HNV H0 H3 HX x' H1).
    Qed.

  End dvalue_has_dtyp_ind.

  Definition dtyp_non_void_eqb (t dt : dtyp) :=
    Coqlib.proj_sumbool (NO_VOID_dec t) && dtyp_eqb t dt.

  Fixpoint dvalue_has_dtyp_fun (dv:dvalue) (dt:dtyp) : bool :=
    let list_forallb2 :=
      fix go dvs dts :=
      match dvs, dts with
      | [], [] => true
      | dv::utl, dt::dttl => dvalue_has_dtyp_fun dv dt && go utl dttl
      | _,_ => false
      end
    in

    match dv with
    | DVALUE_Addr a =>
        if dtyp_eq_dec dt DTYPE_Pointer then true else false

    | @DVALUE_I sz x =>
        if dtyp_eq_dec dt (DTYPE_I sz) then true else false

    | DVALUE_IPTR x =>
        if dtyp_eq_dec dt (DTYPE_IPTR) then true else false

    | DVALUE_Double x =>
        if dtyp_eq_dec dt (DTYPE_Double) then true else false

    | DVALUE_Float x =>
        if dtyp_eq_dec dt (DTYPE_Float) then true else false

    | DVALUE_Poison t
    | DVALUE_Oom t =>
        if @NO_VOID_dec t then
          if dtyp_eq_dec dt t then true else false
        else false

    | DVALUE_None =>
        if dtyp_eq_dec dt (DTYPE_Void) then true else false

    | DVALUE_Struct fields =>
        match dt with
        | DTYPE_Struct field_dts =>
            list_forallb2 fields field_dts
        | _ => false
        end

    | DVALUE_Packed_struct fields =>
        match dt with
        | DTYPE_Packed_struct field_dts =>
            list_forallb2 fields field_dts
        | _ => false
        end

    | DVALUE_Array t' elts =>
        match dt with
        | DTYPE_Array sz dtt =>
            if (@NO_VOID_dec dtt) then
              List.forallb (fun u => dvalue_has_dtyp_fun u dtt) elts &&
                (Nat.eqb (List.length elts) (N.to_nat sz)) &&
                dtyp_eqb t' (DTYPE_Array sz dtt)
            else false
        | _ => false
        end

    | DVALUE_Vector t' elts =>
        match dt with
        | DTYPE_Vector sz dtt =>
            if (@NO_VOID_dec dtt) then
              if (@vector_dtyp_dec dtt) then
                List.forallb (fun u => dvalue_has_dtyp_fun u dtt) elts &&
                  (Nat.eqb (List.length elts) (N.to_nat sz)) &&
                  dtyp_eqb t' (DTYPE_Vector sz dtt)
              else false
            else false
        | _ => false
        end
    end.


  Ltac invert_bools :=
    repeat match goal with
      | [ H : false = true |- _ ] => inversion H
      | [ H : ((?X && ?Y) = true) |- _ ] => apply andb_true_iff in H; destruct H
      | [ H : ((?X || ?Y) = true) |- _ ] => apply orb_true_iff in H; destruct H
    end.


  Lemma dvalue_has_dtyp_fun_sound :
    forall dv dt,
      dvalue_has_dtyp_fun dv dt = true -> dvalue_has_dtyp dv dt.
  Proof using.
    induction dv; intros dtx HX;
      try solve [
          cbn in HX;
          repeat break_match_hyp_inv;
          invert_bools;
          econstructor; eauto with dvalue
        ].

    - cbn in HX.
      repeat break_match_hyp_inv.
      constructor.
      revert fields0 H1.
      induction fields; intros fields0 H1.
      + subst. break_match_hyp_inv.
        constructor.
      + subst. break_match_hyp_inv.
        invert_bools.
        constructor.
        eapply H; eauto. constructor. reflexivity.
        eapply IHfields; auto.
        intros.
        eapply H.
        right.  assumption. assumption.

    - cbn in HX.
      repeat break_match_hyp_inv.
      constructor.
      revert fields0 H1.
      induction fields; intros fields0 H1.
      + subst. break_match_hyp_inv.
        constructor.
      + subst. break_match_hyp_inv.
        invert_bools.
        constructor.
        eapply H; eauto. constructor. reflexivity.
        eapply IHfields; auto.
        intros.
        eapply H.
        right.  assumption. assumption.

    - cbn in HX.
      repeat break_match_hyp_inv.
      invert_bools.
      apply dtyp_eqb_eq in H1; subst.
      apply DVALUE_Array_typ; auto.
      clear H2.
      induction elts.
      + constructor.
      + cbn in H0.
        invert_bools.
        constructor.
        eapply H; auto. left; auto.
        apply IHelts; auto.
        intros.
        eapply H. right; auto.
        assumption.
      + apply Nat.eqb_eq in H2.
        assumption.
    - cbn in HX.
      repeat break_match_hyp_inv.
      invert_bools.
      apply dtyp_eqb_eq in H1; subst.
      apply DVALUE_Vector_typ; auto.
      clear H2.
      induction elts.
      + constructor.
      + cbn in H0.
        invert_bools.
        constructor.
        eapply H; auto. left; auto.
        apply IHelts; auto.
        intros.
        eapply H. right; auto.
        assumption.
      + apply Nat.eqb_eq in H2.
        assumption.
  Qed.

  Ltac forward_bools :=
    repeat match goal with
        [ |- ((?X && ?Y) = true) ] => apply andb_true_iff; split
      | [ |- ((?X || ?Y) = true)  ] => apply orb_true_iff
      end.

  Ltac invert_hyps :=
    repeat match goal with
        [ H : (?P /\ ?Q) |- _ ] => destruct H
      | [ H : (?P \/ ?Q) |- _ ] => destruct H
      end.

  Lemma dvalue_has_dtyp_fun_complete :
    forall dv dt,
      dvalue_has_dtyp dv dt -> dvalue_has_dtyp_fun dv dt = true.
  Proof using.
    intros dv dt TYPE.
    induction TYPE; auto;
      try solve [
          cbn; induction H; forward_bools; auto
        | cbn; repeat break_match_goal; auto; try contradiction;
          forward_bools; [rewrite forallb_forall; auto | apply Nat.eqb_eq; auto | apply dtyp_eqb_refl]
        | cbn; repeat break_match_goal; auto
        | cbn;
          repeat break_match_goal; invert_hyps; subst;
          try (inversion H0; subst; try contradiction);
          try (solve [inversion H]);
          forward_bools; auto
        ].
  Qed.


  Lemma dvalue_has_dtyp_dec :
    forall dv dt,
      {dvalue_has_dtyp dv dt} + {~ dvalue_has_dtyp dv dt}.
  Proof using.
    intros.
    destruct (dvalue_has_dtyp_fun dv dt) eqn:H.
    left. apply dvalue_has_dtyp_fun_sound; auto.
    right. intros C. apply dvalue_has_dtyp_fun_complete in C.
    rewrite H in C. inversion C.
  Qed.

  Definition trunc_base_okb from_dt to_dt :=
    match from_dt with
    | DTYPE_I from_sz =>
        match to_dt with
        | DTYPE_I to_sz => Pos.ltb to_sz from_sz
        | _ => false
        end
    | DTYPE_IPTR =>
        match to_dt with
        | DTYPE_I to_sz =>
            (* TODO: This is a little dodgy... Can we always truncate? What about finite iptrs? *)
            true
        | _ => false
        end
    | _ => false
    end.

  Definition lift_conv_okb conv_base_okb from_dt to_dt :=
    match from_dt with
    | DTYPE_Vector from_n from_vdt =>
        match to_dt with
        | DTYPE_Vector to_n to_vdt =>
            conv_base_okb from_vdt to_vdt
        | _ => false
        end
    | _ => conv_base_okb from_dt to_dt
    end.

  Definition ext_base_okb from_dt to_dt :=
    match from_dt with
    | DTYPE_I from_sz =>
        match to_dt with
        | DTYPE_I to_sz => Pos.ltb from_sz to_sz
        | DTYPE_IPTR =>
            (* TODO: A little dodgy too... *)
            true
        | _ => false
        end
    | _ => false
    end.

  (* SAZ: TODO - add the other conversion operations *)
  Definition conversion_okb (conv : LLVMAst.conversion_type) (from_dt to_dt : dtyp)  : bool :=
    match conv with
    | Trunc => lift_conv_okb trunc_base_okb from_dt to_dt
    | Zext
    | Sext => lift_conv_okb ext_base_okb from_dt to_dt
    | _ => false
    end.

  (* Assumes:
     [l] is a list of indices treated as a path into the nested structure.
     The function returns true iff the type at the index is equal to [dt]

  *)
  Fixpoint fetch_extract_path l dt_src : err dtyp :=
    match l with
    | [] => failwith "fetch_extract_path: no path"
    | [idx] =>
        if (Z.ltb idx 0) then failwith "fetch_extract_path: negative index"
        else
          match dt_src with
          | DTYPE_Array len t =>
              if (N.ltb (Z.to_N idx) len) then ret t
              else failwith "fetch_extract_path: array out of bounds"
          | DTYPE_Struct fts
          | DTYPE_Packed_struct fts =>
              if Nat.ltb (Z.to_nat idx) (length fts)
              then ret (List.nth (Z.to_nat idx) fts DTYPE_Void)
              else failwith "fetch_extract_path: struct out of bounds"
          | _ => failwith "fetch_extract_path: invalid type"
          end
    | idx::idxs =>
        if (Z.ltb idx 0) then failwith "fetch_extract_path: negative index"
        else
          match dt_src with
          | DTYPE_Array len t =>
              if (N.ltb (Z.to_N idx) len)
              then fetch_extract_path idxs t
              else failwith "fetch_extract_path: array out of bounds"
          | DTYPE_Struct fts
          | DTYPE_Packed_struct fts =>
              if Nat.ltb (Z.to_nat idx) (length fts)
              then let nth_ft := List.nth (Z.to_nat idx) fts DTYPE_Void in
                   fetch_extract_path idxs nth_ft
              else failwith "fetch_extract_path: struct out of bounds"
          | _ => failwith "fetch_extract_path: invalid type"
          end
    end.

  Definition check_extract_path l dt_src dt_tgt :=
    match fetch_extract_path l dt_src with
    | inr t => dtyp_eqb t dt_tgt
    | _ => false
    end.

  Lemma check_fetch_extract_path :
    forall idxs d dtx,
      fetch_extract_path idxs d = inr dtx <-> check_extract_path idxs d dtx = true.
  Proof.
    intros idxs d dtx.
    split.
    - intros FETCH.
      unfold check_extract_path.
      rewrite FETCH.
      apply dtyp_eqb_refl.
    - intros CHECK.
      unfold check_extract_path in CHECK.
      break_match_hyp_inv.
      apply dtyp_eqb_eq in H0; subst; auto.
  Qed.

  Unset Elimination Schemes.
  Inductive uvalue_has_dtyp : uvalue -> dtyp -> Prop :=
  | UVALUE_Addr_typ   : forall a, uvalue_has_dtyp (UVALUE_Addr a) DTYPE_Pointer
  | UVALUE_I_typ      : forall sz x, uvalue_has_dtyp (@UVALUE_I sz x) (DTYPE_I sz)
  | UVALUE_IPTR_typ    : forall x, uvalue_has_dtyp (UVALUE_IPTR x) (DTYPE_IPTR)
  | UVALUE_Double_typ : forall x, uvalue_has_dtyp (UVALUE_Double x) DTYPE_Double
  | UVALUE_Float_typ  : forall x, uvalue_has_dtyp (UVALUE_Float x) DTYPE_Float
  | UVALUE_None_typ   : uvalue_has_dtyp UVALUE_None DTYPE_Void
  | UVALUE_Poison_typ : forall τ, NO_VOID τ -> uvalue_has_dtyp (UVALUE_Poison τ) τ
  | UVALUE_Oom_typ    : forall τ, NO_VOID τ -> uvalue_has_dtyp (UVALUE_Oom τ) τ
  | UVALUE_Undef_typ  : forall τ, NO_VOID τ -> uvalue_has_dtyp (UVALUE_Undef τ) τ

  | UVALUE_Struct_typ :
    forall fields dts,
      List.Forall2 uvalue_has_dtyp fields dts ->
      uvalue_has_dtyp (UVALUE_Struct fields) (DTYPE_Struct dts)

  | UVALUE_Pacted_struct_typ :
    forall fields dts,
      List.Forall2 uvalue_has_dtyp fields dts ->
      uvalue_has_dtyp (UVALUE_Packed_struct fields) (DTYPE_Packed_struct dts)

  (* Do we have to exclude mmx? "There are no arrays, vectors or constants of this type" *)
  | UVALUE_Array_typ :
    forall xs sz dt,
      NO_VOID dt ->
      Forall (fun x => uvalue_has_dtyp x dt) xs ->
      length xs = (N.to_nat sz) ->
      uvalue_has_dtyp (UVALUE_Array (DTYPE_Array sz dt) xs) (DTYPE_Array sz dt)

  | UVALUE_Vector_typ :
      forall xs sz dt,
        NO_VOID dt ->
        Forall (fun x => uvalue_has_dtyp x dt) xs ->
        length xs = (N.to_nat sz) ->
        vector_dtyp dt ->
        uvalue_has_dtyp (UVALUE_Vector (DTYPE_Vector sz dt) xs) (DTYPE_Vector sz dt)

  | UVALUE_IBinop_typ :
      forall x y sz op dt,
      (dt = (DTYPE_I sz) \/ dt = DTYPE_IPTR) ->
      uvalue_has_dtyp x dt ->
      uvalue_has_dtyp y dt ->
      uvalue_has_dtyp (UVALUE_IBinop op x y) dt

  | UVALUE_IBinop_vector_typ :
      forall x y vsz (isz : positive) op dt,
      (dt = (DTYPE_I isz) \/ dt = DTYPE_IPTR) ->
      uvalue_has_dtyp x (DTYPE_Vector vsz dt) ->
      uvalue_has_dtyp y (DTYPE_Vector vsz dt) ->
      uvalue_has_dtyp (UVALUE_IBinop op x y) (DTYPE_Vector vsz dt)

  | UVALUE_ICmp_typ :
      forall x y op sz,
        ((uvalue_has_dtyp x (DTYPE_I sz) /\ uvalue_has_dtyp y (DTYPE_I sz))
         \/
           (uvalue_has_dtyp x DTYPE_IPTR /\ uvalue_has_dtyp y DTYPE_IPTR)
         \/
         (uvalue_has_dtyp x DTYPE_Pointer /\ uvalue_has_dtyp y DTYPE_Pointer)) ->
        uvalue_has_dtyp (UVALUE_ICmp op x y) (DTYPE_I 1)

  | UVALUE_ICmp_vector_typ :
      forall x y vsz isz op,
        ((uvalue_has_dtyp x (DTYPE_Vector vsz (DTYPE_I isz)) /\
            uvalue_has_dtyp y (DTYPE_Vector vsz (DTYPE_I isz)))
         \/
           (uvalue_has_dtyp x (DTYPE_Vector vsz DTYPE_IPTR) /\
              uvalue_has_dtyp y (DTYPE_Vector vsz DTYPE_IPTR))
         \/
           (uvalue_has_dtyp x (DTYPE_Vector vsz DTYPE_Pointer) /\
              uvalue_has_dtyp y (DTYPE_Vector vsz DTYPE_Pointer))
        ) ->
      uvalue_has_dtyp (UVALUE_ICmp op x y) (DTYPE_Vector vsz (DTYPE_I 1))

  | UVALUE_FBinop_typ :
    forall x y op fms dt,
      (dt = DTYPE_Double \/ dt = DTYPE_Float) ->
      uvalue_has_dtyp x dt ->
      uvalue_has_dtyp y dt ->
      uvalue_has_dtyp (UVALUE_FBinop op fms x y) dt

  | UVALUE_FBinop_vector_typ :
    forall x y vsz op fms dt,
      (dt = DTYPE_Double \/ dt = DTYPE_Float) ->
      uvalue_has_dtyp x (DTYPE_Vector vsz dt) ->
      uvalue_has_dtyp y (DTYPE_Vector vsz dt) ->
      uvalue_has_dtyp (UVALUE_FBinop op fms x y) (DTYPE_Vector vsz dt)

  | UVALUE_FCmp_typ :
    forall x y op dt,
      (dt = DTYPE_Double \/ dt = DTYPE_Float) ->
      uvalue_has_dtyp x dt ->
      uvalue_has_dtyp y dt ->
      uvalue_has_dtyp (UVALUE_FCmp op x y) (DTYPE_I 1)

  | UVALUE_FCmp_vector_typ :
      forall x y vsz op,
        ((uvalue_has_dtyp x (DTYPE_Vector vsz (DTYPE_Double)) /\
            uvalue_has_dtyp y (DTYPE_Vector vsz (DTYPE_Double)))
         \/
           (uvalue_has_dtyp x (DTYPE_Vector vsz DTYPE_Float) /\
              uvalue_has_dtyp y (DTYPE_Vector vsz DTYPE_Float))
        ) ->
      uvalue_has_dtyp (UVALUE_FCmp op x y) (DTYPE_Vector vsz (DTYPE_I 1))

  | UVALUE_Conversion_typ :
    forall conv from_typ value to_typ,
      uvalue_has_dtyp value from_typ ->
      conversion_okb conv from_typ to_typ = true ->
      uvalue_has_dtyp (UVALUE_Conversion conv from_typ value to_typ) to_typ

  | UVALUE_GetElementPtr_typ :
    forall dt uv idxs,
      uvalue_has_dtyp (UVALUE_GetElementPtr dt uv idxs) DTYPE_Pointer

  | UVALUE_ExtractElement_typ :
      forall n vect idx t sz,
        ((uvalue_has_dtyp idx (DTYPE_I sz))
         \/
           uvalue_has_dtyp idx DTYPE_IPTR
         ) ->
        uvalue_has_dtyp vect (DTYPE_Vector n t) ->
        uvalue_has_dtyp (UVALUE_ExtractElement (DTYPE_Vector n t) vect idx) t

  | UVALUE_InsertElement_typ :
      forall n vect val idx t sz,
        ((uvalue_has_dtyp idx (DTYPE_I sz))
         \/
           uvalue_has_dtyp idx DTYPE_IPTR
         ) ->
        uvalue_has_dtyp vect (DTYPE_Vector n t) ->
        uvalue_has_dtyp val t ->
        uvalue_has_dtyp (UVALUE_InsertElement (DTYPE_Vector n t) vect val idx) (DTYPE_Vector n t)

  | UVALUE_ShuffleVector_typ :
    forall n m v1 v2 idxs t,
      uvalue_has_dtyp idxs (DTYPE_Vector m (DTYPE_I 32)) ->
      uvalue_has_dtyp v1 (DTYPE_Vector n t) ->
      uvalue_has_dtyp v2 (DTYPE_Vector n t) ->
      uvalue_has_dtyp (UVALUE_ShuffleVector (DTYPE_Vector n t) v1 v2 idxs) (DTYPE_Vector m t)

  | UVALUE_ExtractValue_typ :
    forall dt_agg uv path dt,
      uvalue_has_dtyp uv dt_agg ->
      check_extract_path path dt_agg dt = true ->
      uvalue_has_dtyp (UVALUE_ExtractValue dt_agg uv path) dt

  | UVALUE_InsertValue_typ :
      forall dt_agg uv dt_elt elt path,
        uvalue_has_dtyp elt dt_elt ->
        uvalue_has_dtyp uv dt_agg ->
        check_extract_path path dt_agg dt_elt = true ->
        uvalue_has_dtyp (UVALUE_InsertValue dt_agg uv dt_elt elt path) dt_agg

  | UVALUE_Select_i1 :
    forall cond x y t,
      uvalue_has_dtyp cond (DTYPE_I 1) ->
      uvalue_has_dtyp x t ->
      uvalue_has_dtyp y t ->
      uvalue_has_dtyp (UVALUE_Select cond x y) t

  | UVALUE_Select_vect :
      forall cond x y t sz,
        uvalue_has_dtyp cond (DTYPE_Vector sz (DTYPE_I 1)) ->
        uvalue_has_dtyp x (DTYPE_Vector sz t) ->
        uvalue_has_dtyp y (DTYPE_Vector sz t) ->
        uvalue_has_dtyp (UVALUE_Select cond x y) (DTYPE_Vector sz t)

  (* Maybe ExtractByte just doesn't have a type because no values should be raw ExtractByte values... *)
  (* | UVALUE_ExtractByte_typ : *)
  (*     forall uv dt idx sid, *)
  (*       uvalue_has_dtyp (UVALUE_ExtractByte uv dt idx sid) (DTYPE_I 8) *)
  | UVALUE_ConcatBytes_typ :
    forall bytes dt,
      (forall byte, In byte bytes -> exists uv t idx sid, byte = UVALUE_ExtractByte uv t idx sid) ->
      N.of_nat (length bytes) = sizeof_dtyp dt ->
      uvalue_has_dtyp (UVALUE_ConcatBytes bytes dt) dt.

  Section uvalue_has_dtyp_ind.
    Variable P : uvalue -> dtyp -> Prop.
    Hypothesis IH_Addr           : forall a, P (UVALUE_Addr a) DTYPE_Pointer.
    Hypothesis IH_I              : forall sz x, P (@UVALUE_I sz x) (DTYPE_I sz).
    Hypothesis IH_IPTR           : forall x, P (UVALUE_IPTR x) DTYPE_IPTR.
    Hypothesis IH_Double         : forall x, P (UVALUE_Double x) DTYPE_Double.
    Hypothesis IH_Float          : forall x, P (UVALUE_Float x) DTYPE_Float.
    Hypothesis IH_None           : P UVALUE_None DTYPE_Void.
    Hypothesis IH_Poison         : forall τ, NO_VOID τ -> P (UVALUE_Poison τ) τ.
    Hypothesis IH_Oom            : forall τ, NO_VOID τ -> P (UVALUE_Oom τ) τ.
    Hypothesis IH_Undef          : forall τ, NO_VOID τ -> P (UVALUE_Undef τ) τ.

    Hypothesis IH_Struct :
      forall fields fts,
        List.Forall2 P fields fts ->
        P (UVALUE_Struct fields) (DTYPE_Struct fts).

    Hypothesis IH_Packed_struct :
      forall fields fts,
        List.Forall2 P fields fts ->
        P (UVALUE_Packed_struct fields) (DTYPE_Packed_struct fts).

    Hypothesis IH_Array : forall (xs : list uvalue)
                             sz
                            (dt : dtyp)
                            (IH : forall x, In x xs -> P x dt),
        NO_VOID dt ->
        Datatypes.length xs = (N.to_nat sz) ->
        P (UVALUE_Array (DTYPE_Array sz dt) xs) (DTYPE_Array sz dt).

    Hypothesis IH_Vector : forall (xs : list uvalue) sz (dt : dtyp)
                             (IH : forall x, In x xs -> P x dt),
        NO_VOID dt ->
        Datatypes.length xs = (N.to_nat sz) ->
        vector_dtyp dt -> P (UVALUE_Vector (DTYPE_Vector sz dt) xs) (DTYPE_Vector sz dt).

    Hypothesis IH_IBinop : forall (x y : uvalue) (sz : positive) (op : ibinop) dt,
        ((dt = (DTYPE_I sz)) \/ (dt = DTYPE_IPTR)) ->
        P x dt ->
        P y dt ->
        P (UVALUE_IBinop op x y) dt.

    Hypothesis IH_IBinop_vector : forall (x y : uvalue) vsz (sz : positive) (op : ibinop) dt,
        ((dt = (DTYPE_I sz)) \/ (dt = DTYPE_IPTR)) ->
        P x (DTYPE_Vector vsz dt) ->
        P y (DTYPE_Vector vsz dt) ->
        P (UVALUE_IBinop op x y) (DTYPE_Vector vsz dt).

    Hypothesis IH_ICmp :
          forall x y op sz,
        ((P x (DTYPE_I sz) /\ P y (DTYPE_I sz))
         \/
           (P x DTYPE_IPTR /\ P y DTYPE_IPTR)
         \/
         (P x DTYPE_Pointer /\ P y DTYPE_Pointer)) ->
        P (UVALUE_ICmp op x y) (DTYPE_I 1).

    Hypothesis IH_ICmp_vector : forall x y vsz isz op,
        ((P x (DTYPE_Vector vsz (DTYPE_I isz)) /\
            P y (DTYPE_Vector vsz (DTYPE_I isz)))
         \/
           (P x (DTYPE_Vector vsz DTYPE_IPTR) /\
              P y (DTYPE_Vector vsz DTYPE_IPTR))
         \/
           (P x (DTYPE_Vector vsz DTYPE_Pointer) /\
              P y (DTYPE_Vector vsz DTYPE_Pointer))
        ) ->
      P (UVALUE_ICmp op x y) (DTYPE_Vector vsz (DTYPE_I 1)).

    Hypothesis IH_FBinop : forall (x y : uvalue) (op : fbinop) (fms : list fast_math) dt,
        (dt = DTYPE_Double \/ dt = DTYPE_Float) ->
        P x dt ->
        P y dt ->
        P (UVALUE_FBinop op fms x y) dt.

    Hypothesis IH_FBinop_vector : forall (x y : uvalue) vsz (op : fbinop) (fms : list fast_math) dt,
        (dt = DTYPE_Double \/ dt = DTYPE_Float) ->
        P x (DTYPE_Vector vsz dt) ->
        P y (DTYPE_Vector vsz dt) ->
        P (UVALUE_FBinop op fms x y) (DTYPE_Vector vsz dt).

    Hypothesis IH_FCmp : forall (x y : uvalue) (op : fcmp) dt,
        (dt = DTYPE_Double \/ dt = DTYPE_Float) ->
        P x dt ->
        P y dt ->
        P (UVALUE_FCmp op x y) (DTYPE_I 1).

    Hypothesis IH_FCmp_vector : forall (x y : uvalue) vsz (op : fcmp) dt,
        (dt = DTYPE_Double \/ dt = DTYPE_Float) ->
        P x (DTYPE_Vector vsz dt) ->
        P y (DTYPE_Vector vsz dt) ->
        P (UVALUE_FCmp op x y) (DTYPE_Vector vsz (DTYPE_I 1)).

    Hypothesis IH_Conversion : forall conv from_typ value to_typ,
        P value from_typ ->
        conversion_okb conv from_typ to_typ = true ->
        P (UVALUE_Conversion conv from_typ value to_typ) to_typ.

    Hypothesis IH_GetElementPtr : forall (dt : dtyp) (uv : uvalue) (idxs : list uvalue),
        P (UVALUE_GetElementPtr dt uv idxs) DTYPE_Pointer.

    Hypothesis IH_ExtractElement : forall n (vect idx : uvalue) (t : dtyp) (sz : positive),
        ((P idx (DTYPE_I sz))
         \/
           P idx DTYPE_IPTR
         ) ->
        P vect (DTYPE_Vector n t) ->
        P (UVALUE_ExtractElement (DTYPE_Vector n t) vect idx) t.

    Hypothesis IH_InsertElement : forall n (vect val idx : uvalue) (t : dtyp) (sz : positive),
        ((P idx (DTYPE_I sz))
         \/
           P idx DTYPE_IPTR
         ) ->
        P vect (DTYPE_Vector n t) ->
        P val t ->
        P (UVALUE_InsertElement (DTYPE_Vector n t) vect val idx) (DTYPE_Vector n t).

    Hypothesis IH_ShuffleVector : forall n m (v1 v2 idxs : uvalue) (t : dtyp),
        P idxs (DTYPE_Vector m (DTYPE_I 32)) ->
        P v1 (DTYPE_Vector n t) ->
        P v2 (DTYPE_Vector n t) ->
        P (UVALUE_ShuffleVector (DTYPE_Vector n t) v1 v2 idxs) (DTYPE_Vector m t).

    Hypothesis IH_ExtractValue :
    forall dt_agg uv path dt,
      P uv dt_agg ->
      uvalue_has_dtyp uv dt_agg ->  (* not strictly necessary, but useful *)
      check_extract_path path dt_agg dt = true ->
      P (UVALUE_ExtractValue dt_agg uv path) dt.

    Hypothesis IH_InsertValue :
      forall dt_agg uv dt_elt elt path,
        P elt dt_elt ->
        P uv dt_agg ->
        uvalue_has_dtyp uv dt_agg -> (* not strictly necessary, but useful *)
        check_extract_path path dt_agg dt_elt = true ->
        P (UVALUE_InsertValue dt_agg uv dt_elt elt path) dt_agg.

    Hypothesis IH_Select_i1 : forall (cond x y : uvalue) (t : dtyp),
        P cond (DTYPE_I 1) ->
        P x t ->
        P y t ->
        P (UVALUE_Select cond x y) t.

    Hypothesis IH_Select_vect : forall (cond x y : uvalue) (t : dtyp) sz,
        P cond (DTYPE_Vector sz (DTYPE_I 1)) ->
        P x (DTYPE_Vector sz t) ->
        P y (DTYPE_Vector sz t) ->
        P (UVALUE_Select cond x y) (DTYPE_Vector sz t).

    (* Hypothesis IH_UVALUE_ExtractByte : *)
    (*   forall uv dt idx sid, *)
    (*     P (UVALUE_ExtractByte uv dt idx sid) (DTYPE_I 8). *)

    Hypothesis IH_UVALUE_ConcatBytes :
      forall bytes dt,
        (forall byte, In byte bytes -> exists uv t idx sid, byte = UVALUE_ExtractByte uv t idx sid) ->
        N.of_nat (length bytes) = sizeof_dtyp dt ->
        P (UVALUE_ConcatBytes bytes dt) dt.

    Lemma uvalue_has_dtyp_ind : forall (uv:uvalue) (dt:dtyp) (TYP: uvalue_has_dtyp uv dt),  P uv dt.
      fix IHQ 3.
      intros uv dt TYP.
      destruct TYP;
        try (solve [let IH := fresh in
                    remember (forall (uv : uvalue) (dt : dtyp), uvalue_has_dtyp uv dt -> P uv dt) as IH;
                    match goal with
                    | H: _ |- _ =>
                      solve [eapply H; subst IH; eauto]
                    end]).

      - apply IH_Struct.
        revert fields dts H.
        fix IHL_A 3.
        intros fields dts H.
        destruct H.
        + constructor.
        + constructor.
          eauto.
          eauto.

      - apply IH_Packed_struct.
        revert fields dts H.
        fix IHL_A 3.
        intros fields dts H.
        destruct H.
        + constructor.
        + constructor.
          eauto.
          eauto.

      - apply IH_Array; auto.
        revert xs sz dt H H0 H1.
        fix IHL_C 5.
        intros xs sz dt HNV H EQ .
        destruct H.
        * intros x HIN. inversion HIN.
        * intros x' HIN. inversion HIN.
          -- rewrite <- H1.
             eapply IHQ.
             assumption.

          -- simpl in EQ.
             destruct (N.to_nat sz); inversion EQ.
             rewrite <- Nnat.Nat2N.id in H3.
             apply (IHL_C _ _ _ HNV H0 H3 x' H1).

      - apply IH_Vector; auto.
        revert xs sz dt H H0 H1 H2.
        fix IHL_C 5.
        intros xs sz dt HNV H EQ HX.
        destruct H.
        * intros x HIN. inversion HIN.
        * intros x' HIN. inversion HIN.
          -- rewrite <- H1.
             eapply IHQ.
             assumption.

          -- simpl in EQ.
             destruct (N.to_nat sz); inversion EQ.
             rewrite <- Nnat.Nat2N.id in H3.
             apply (IHL_C _ _ _ HNV H0 H3 HX x' H1).

      - destruct H as [[HX HY]|[[HX HY]|[HX HY]]].
        + eapply IH_ICmp with (sz := sz).
          left. split; eauto.
        + eapply IH_ICmp with (sz := sz).
          right. left; split; eauto.
        + eapply IH_ICmp with (sz := sz).
          right. right; split; eauto.

      - eapply IH_ICmp_vector.
        destruct H as [[HX HY]|[[HX HY]|[HX HY]]].
        + left; split; eauto.
        + right. left; split; eauto.
        + right. right; split; eauto.

      - destruct H as [[HX HY]|[HX HY]].
        + eapply IH_FCmp_vector with (dt:=DTYPE_Double); auto.
        + eapply IH_FCmp_vector with (dt:=DTYPE_Float); auto.

      - eapply IH_ExtractElement with (sz:=sz); auto.
        destruct H as [HI | HI].
        + left. eapply IHQ. apply HI.
        + right. eapply IHQ. apply HI.

      - eapply IH_InsertElement with (sz:=sz); auto.
        destruct H as [HI | HI].
        + left. eapply IHQ. apply HI.
        + right. eapply IHQ. apply HI.
    Qed.

  End uvalue_has_dtyp_ind.

  #[global]
    Hint Constructors uvalue_has_dtyp : uvalue.

  Definition valid_ibinop_type (t : dtyp) : bool :=
    match t with
    | DTYPE_I _
    | DTYPE_IPTR
    | DTYPE_Vector _ (DTYPE_I _)
    | DTYPE_Vector _ (DTYPE_IPTR) =>
        true
    | _ => false
    end.

  Definition valid_icmp_type (t : dtyp) : bool :=
    match t with
    | DTYPE_I _
    | DTYPE_IPTR
    | DTYPE_Pointer
    | DTYPE_Vector _ (DTYPE_I _)
    | DTYPE_Vector _ (DTYPE_Pointer)
    | DTYPE_Vector _ (DTYPE_IPTR) =>
        true
    | _ => false
    end.

  Definition valid_fbinop_type (t : dtyp) : bool :=
    match t with
    | DTYPE_Float
    | DTYPE_Double
    | DTYPE_Vector _ DTYPE_Float
    | DTYPE_Vector _ DTYPE_Double =>
        true
    | _ => false
    end.

  Fixpoint dtyp_of_uvalue_fun (uv:uvalue) : err dtyp :=
    let list_dtyps :=
      fix go (uvs : list uvalue) : err (list dtyp) :=
        match uvs with
        | [] => inr []
        | uv::utl =>
            dt <- dtyp_of_uvalue_fun uv;;
            dts <- go utl;;
            ret (dt :: dts)
        end
    in

    match uv with
    | UVALUE_Addr a => ret DTYPE_Pointer  
    | @UVALUE_I sz x => ret (DTYPE_I sz)
    | UVALUE_IPTR x => ret DTYPE_IPTR
    | UVALUE_Double x => ret DTYPE_Double
    | UVALUE_Float x => ret DTYPE_Float
    | UVALUE_Undef t
    | UVALUE_Poison t
    | UVALUE_Oom t =>
        if @NO_VOID_dec t then
          ret t
        else
          inl "dtyp_of_uvalue_fun: void undef / poison / oom type"
    | UVALUE_None => ret DTYPE_Void
    | UVALUE_Struct fields =>
        dts <- list_dtyps fields;;
        ret (DTYPE_Struct dts)
    | UVALUE_Packed_struct fields =>
        dts <- list_dtyps fields;;
        ret (DTYPE_Packed_struct dts)
    | UVALUE_Array (DTYPE_Array sz t) elts =>
        if @NO_VOID_dec t
        then
          if forallb (fun e => match dtyp_of_uvalue_fun e with | inr t' => dtyp_eqb t t' | _ => false end) elts && N.eqb sz (N.of_nat (length elts))
          then ret (DTYPE_Array (N.of_nat (length elts)) t)
          else inl "dtyp_of_uvalue_fun: mismatched element type in array"
        else inl "dtyp_of_uvalue_fun: void in array type"
    | UVALUE_Vector (DTYPE_Vector sz t) elts =>
        if @NO_VOID_dec t
        then
          if forallb (fun e => match dtyp_of_uvalue_fun e with | inr t' => dtyp_eqb t t' | _ => false end) elts && N.eqb sz (N.of_nat (length elts))
          then
            if @vector_dtyp_dec t
            then ret (DTYPE_Vector (N.of_nat (length elts)) t)
            else inl "dtyp_of_uvalue_fun: invalid element type for vector"
          else inl "dtyp_of_uvalue_fun: mismatched element type in vector"
        else inl "dtyp_of_uvalue_fun: void in vector type"
    | UVALUE_IBinop iop x y =>
        t1 <- dtyp_of_uvalue_fun x;;
        t2 <- dtyp_of_uvalue_fun y;;
        if dtyp_eqb t1 t2 && valid_ibinop_type t1
        then ret t1
        else inl "dtyp_of_uvalue_fun: mismatched ibinop types"

    | UVALUE_ICmp op x y =>
        t1 <- dtyp_of_uvalue_fun x;;
        t2 <- dtyp_of_uvalue_fun y;;
        if dtyp_eqb t1 t2 && valid_icmp_type t1
        then
          match t1 with
          | DTYPE_Vector vsz _ =>
              ret (DTYPE_Vector vsz (DTYPE_I 1))
          | _ =>
              ret (DTYPE_I 1)
          end
        else inl "dtyp_of_uvalue_fun: mismatched icmp types"

    | UVALUE_FBinop op fms x y =>
        t1 <- dtyp_of_uvalue_fun x;;
        t2 <- dtyp_of_uvalue_fun y;;
        if dtyp_eqb t1 t2 && valid_fbinop_type t1
        then ret t1
        else inl "dtyp_of_uvalue_fun: mismatched fbinop types"

    | UVALUE_FCmp op x y =>
        t1 <- dtyp_of_uvalue_fun x;;
        t2 <- dtyp_of_uvalue_fun y;;
        if dtyp_eqb t1 t2 && valid_fbinop_type t1
        then
          match t1 with
          | DTYPE_Vector vsz _ =>
              ret (DTYPE_Vector vsz (DTYPE_I 1))
          | _ =>
              ret (DTYPE_I 1)
          end
        else inl "dtyp_of_uvalue_fun: mismatched fcmp types"

    | UVALUE_Conversion conv from_dt value to_dt =>
        t <- dtyp_of_uvalue_fun value;;
        if dtyp_eqb t from_dt && conversion_okb conv from_dt to_dt
        then ret to_dt
        else inl "dtyp_of_uvalue_fun: ill-typed conversion"

    | UVALUE_GetElementPtr agg_dt uv idxs =>
        ret DTYPE_Pointer

    | UVALUE_ExtractElement (DTYPE_Vector n t) vect idx =>
        t_idx <- dtyp_of_uvalue_fun idx;;
        match t_idx with
        | (DTYPE_I _)
        | DTYPE_IPTR =>
            t_vect <- dtyp_of_uvalue_fun vect;;
            if dtyp_eq_dec (DTYPE_Vector n t) t_vect
            then ret t
            else inl "dtyp_of_uvalue_fun: ill-typed vector for extractelement"
        | _ => inl "dtyp_of_uvalue_fun: ill-typed index for extractelement"
        end

    | UVALUE_InsertElement (DTYPE_Vector n t) vect val idx =>
        t_idx <- dtyp_of_uvalue_fun idx;;
        match t_idx with
        | (DTYPE_I _)
        | DTYPE_IPTR =>
            t_vect <- dtyp_of_uvalue_fun vect;;
            t_val <- dtyp_of_uvalue_fun val;;
            if dtyp_eqb (DTYPE_Vector n t) t_vect && dtyp_eqb t_val t
            then ret t_vect
            else inl "dtyp_of_uvalue_fun: ill-typed insertelement"
        | _ => inl "dtyp_of_uvalue_fun: ill-typed index for insertelement"
        end

    | UVALUE_ShuffleVector (DTYPE_Vector n t) v1 v2 idxs =>
        match dtyp_of_uvalue_fun idxs with
        | inr (DTYPE_Vector m (DTYPE_I 32))  =>
            t_v1 <- dtyp_of_uvalue_fun v1;;
            t_v2 <- dtyp_of_uvalue_fun v2;;
            if dtyp_eqb (DTYPE_Vector n t) t_v1 && dtyp_eqb t_v1 t_v2
            then ret (DTYPE_Vector m t)
            else failwith "dtyp_of_uvalue_fun: invalid shufflevector"
        | _ => failwith "dtyp_of_uvalue_fun: invalid shufflevector"
        end

    | UVALUE_ExtractValue dt_agg uv path =>
        t_uv <- dtyp_of_uvalue_fun uv;;
        if dtyp_eq_dec dt_agg t_uv
        then fetch_extract_path path dt_agg
        else inl "dtyp_of_uvalue_fun: extractvalue type mismatch"

    | UVALUE_InsertValue dt_agg uv dt_elt elt path =>
        t_uv <- dtyp_of_uvalue_fun uv;;
        t_elt <- dtyp_of_uvalue_fun elt;;
        if dtyp_eqb dt_agg t_uv && dtyp_eqb dt_elt t_elt && check_extract_path path dt_agg dt_elt
        then ret dt_agg
        else inl "dtyp_of_uvalue_fun: insertvalue type mismatch"

    | UVALUE_Select cond x y =>
        tcond <- dtyp_of_uvalue_fun cond;;
        match tcond with
        | DTYPE_I 1 =>
            t1 <- dtyp_of_uvalue_fun x;;
            t2 <- dtyp_of_uvalue_fun y;;
            if dtyp_eq_dec t1 t2
            then ret t1
            else inl "dtyp_of_uvalue_fun: select type mismatch"
        | DTYPE_Vector sz (DTYPE_I 1) =>
            t1 <- dtyp_of_uvalue_fun x;;
            match t1 with
            | DTYPE_Vector sz' t' =>
                if N.eq_dec sz sz'
                then
                  t2 <- dtyp_of_uvalue_fun y;;
                  if dtyp_eq_dec t1 t2
                  then ret t1
                  else inl "dtyp_of_uvalue_fun: select type mismatch of t1 / t2"
                else inl "dtyp_of_uvalue_fun: select type mismatch of vector sizes"
            | _ => inl "dtyp_of_uvalue_fun: select vector type mismatch"
            end
        | _ => inl "dtyp_of_uvalue_fun: select type mismatch"
        end

    | UVALUE_ConcatBytes bytes t =>
        if (N.of_nat (length bytes) =? sizeof_dtyp t) && forallb (fun byte => match byte with | UVALUE_ExtractByte _ _ _ _ => true | _ => false end) bytes
        then ret t
        else inl "dtyp_of_uvalue_fun: concatbytes type mismatch"

    | _ => failwith "dtyp_of_uvalue_fun: missing case"
    end.

  Definition uvalue_has_dtyp_fun (uv:uvalue) (dt:dtyp) : bool
    := match dtyp_of_uvalue_fun uv with
       | inr dt' => dtyp_eqb dt dt'
       | _ => false
       end.

  Lemma dtyp_of_uvalue_fun_sound :
    forall uv dt,
      dtyp_of_uvalue_fun uv = inr dt -> uvalue_has_dtyp uv dt.
  Proof using.
    induction uv; intros dtx HX;
      try solve [
          unfold uvalue_has_dtyp_fun, dtyp_of_uvalue_fun in HX;
          cbn in HX; try inv HX;
          repeat break_match_hyp_inv;
          econstructor; eauto with uvalue
        ].

    - assert (exists ts, dtx = DTYPE_Struct ts).
      { unfold dtyp_of_uvalue_fun in HX;
          cbn in HX;
          repeat break_match_hyp_inv.
        exists l.
        reflexivity.
      }
      destruct H0 as (ts & DT).
      subst.
      constructor.
      revert ts HX. induction fields; intros ts HX.
      + cbn in HX.
        inv HX.
        constructor.
      + unfold uvalue_has_dtyp_fun, dtyp_of_uvalue_fun in HX;
          cbn in HX.
        repeat (break_inner_match_hyp; try discriminate).
        inv HX.
        cbn.
        forward IHfields.
        { intros u H0 dt H1.
          apply H; cbn; eauto.
        }
        specialize (IHfields l).
        forward IHfields.
        { unfold uvalue_has_dtyp_fun, dtyp_of_uvalue_fun; cbn.
          auto.
          rewrite Heqs0; auto.
        }
        constructor; auto.
        apply H; cbn; auto.
    - assert (exists ts, dtx = DTYPE_Packed_struct ts).
      { unfold dtyp_of_uvalue_fun in HX;
          cbn in HX;
          repeat break_match_hyp_inv.
        exists l.
        reflexivity.
      }
      destruct H0 as (ts & DT).
      subst.
      constructor.
      revert ts HX. induction fields; intros ts HX.
      + cbn in HX.
        inv HX.
        constructor.
      + unfold uvalue_has_dtyp_fun, dtyp_of_uvalue_fun in HX;
          cbn in HX.
        repeat (break_inner_match_hyp; try discriminate).
        inv HX.
        cbn.
        forward IHfields.
        { intros u H0 dt H1.
          apply H; cbn; eauto.
        }
        specialize (IHfields l).
        forward IHfields.
        { unfold uvalue_has_dtyp_fun, dtyp_of_uvalue_fun; cbn.
          auto.
          rewrite Heqs0; auto.
        }
        constructor; auto.
        apply H; cbn; auto.
    - assert (exists d, t = DTYPE_Array (N.of_nat (length elts)) d /\ dtx = t).
      { unfold dtyp_of_uvalue_fun in HX;
          cbn in HX;
          repeat break_match_hyp_inv.
        invert_bools.
        apply N.eqb_eq in H1; subst.
        exists d. auto.
      }
      destruct H0 as (d & ? & ?).
      subst.
      apply UVALUE_Array_typ.
      + unfold dtyp_of_uvalue_fun in HX;
          cbn in HX;
          repeat break_match_hyp_inv; auto.
      + unfold dtyp_of_uvalue_fun in HX;
          cbn in HX;
          repeat break_match_hyp_inv;
          invert_bools;
          auto.
        rename H0 into Heqb.
        apply Forall_forall.
        intros x H0.
        eapply forallb_forall in Heqb; eauto.
        eapply H; eauto.
        break_match_hyp_inv.
        apply dtyp_eqb_eq in H3; subst.
        apply Heqs.
      + rewrite Nnat.Nat2N.id; auto.
    - assert (exists d, t = DTYPE_Vector (N.of_nat (length elts)) d /\ dtx = t).
      { unfold dtyp_of_uvalue_fun in HX;
          cbn in HX;
          repeat break_match_hyp_inv.
        invert_bools.
        apply N.eqb_eq in H1; subst.
        exists d. auto.
      }
      destruct H0 as (d & ? & ?).
      subst.
      apply UVALUE_Vector_typ.
      + unfold dtyp_of_uvalue_fun in HX;
          cbn in HX;
          repeat break_match_hyp_inv; auto.
      + unfold dtyp_of_uvalue_fun in HX;
          cbn in HX;
          repeat break_match_hyp_inv;
          invert_bools;
          auto.
        rename H0 into Heqb.
        apply Forall_forall.
        intros x H0.
        eapply forallb_forall in Heqb; eauto.
        eapply H; eauto.
        break_match_hyp_inv.
        apply dtyp_eqb_eq in H3; subst.
        apply Heqs.
      + rewrite Nnat.Nat2N.id; auto.
      + unfold dtyp_of_uvalue_fun in HX;
          cbn in HX;
          repeat break_match_hyp_inv; auto.

    - cbn in HX;
        repeat break_match_hyp_inv;
        invert_bools;
        unfold valid_ibinop_type in *;
        repeat break_match_hyp_inv;
        repeat match goal with
          | H: dtyp_eqb _ _ = true |- _ =>
              apply dtyp_eqb_eq in H; subst
          end;
        repeat match goal with
          | [ H1 : (forall dt, uvalue_has_dtyp_fun ?UV dt = true -> _),
                H2 : uvalue_has_dtyp_fun ?UV _ = true |- _] => apply H1 in H2
          end.

      all: try solve [econstructor; eauto with uvalue].
    - (* ICmp *)
      cbn in HX.
      do 3 break_match_hyp_inv.
      invert_bools.
      repeat
        match goal with
        | H: dtyp_eqb _ _ = true |- _ =>
            apply dtyp_eqb_eq in H; subst
        end.
      unfold valid_icmp_type in *.
      break_match_hyp_inv; inv H0;
        repeat match goal with
          | [ H1 : (forall dt, uvalue_has_dtyp_fun ?UV dt = true -> _),
                H2 : uvalue_has_dtyp_fun ?UV _ = true |- _] => apply H1 in H2
          end.

      all: try solve [econstructor; eauto with uvalue].
      + eapply UVALUE_ICmp_typ with (sz:=1%positive); right;
        eauto with uvalue.
      + eapply UVALUE_ICmp_typ with (sz:=1%positive); right;
        eauto with uvalue.
      + break_match_hyp_inv.
        * eapply UVALUE_ICmp_vector_typ; eauto with uvalue.
        * eapply UVALUE_ICmp_vector_typ; right; eauto with uvalue.
        * eapply UVALUE_ICmp_vector_typ; right; eauto with uvalue.
    - (* FBinop *)
      cbn in HX;
        repeat break_match_hyp_inv;
        invert_bools;
        unfold valid_fbinop_type in *;
        repeat break_match_hyp_inv;
        repeat match goal with
          | H: dtyp_eqb _ _ = true |- _ =>
              apply dtyp_eqb_eq in H; subst
          end;
        repeat match goal with
          | [ H1 : (forall dt, uvalue_has_dtyp_fun ?UV dt = true -> _),
                H2 : uvalue_has_dtyp_fun ?UV _ = true |- _] => apply H1 in H2
          end.

      all: try solve [econstructor; eauto with uvalue].

    - (*FCmp *)
      cbn in HX.
      do 3 break_match_hyp_inv.
      invert_bools.
      repeat
        match goal with
        | H: dtyp_eqb _ _ = true |- _ =>
            apply dtyp_eqb_eq in H; subst
        end.
      unfold valid_fbinop_type in *.
      break_match_hyp_inv; inv H0;
        repeat match goal with
          | [ H1 : (forall dt, uvalue_has_dtyp_fun ?UV dt = true -> _),
                H2 : uvalue_has_dtyp_fun ?UV _ = true |- _] => apply H1 in H2
          end.

      all: try solve [econstructor; eauto with uvalue].
      + eapply UVALUE_FCmp_typ; try left; eauto with uvalue.
      + break_match_hyp_inv.
        * eapply UVALUE_FCmp_vector_typ; eauto with uvalue.
        * eapply UVALUE_FCmp_vector_typ; left; eauto with uvalue.

    - (* Conversion *)
      cbn in HX;
        repeat break_match_hyp_inv;
        invert_bools;
        unfold valid_ibinop_type in *;
        repeat break_match_hyp_inv;
        repeat match goal with
          | H: dtyp_eqb _ _ = true |- _ =>
              apply dtyp_eqb_eq in H; subst
          end;
        repeat match goal with
          | [ H1 : (forall dt, uvalue_has_dtyp_fun ?UV dt = true -> _),
                H2 : uvalue_has_dtyp_fun ?UV _ = true |- _] => apply H1 in H2
          end.

      all: try solve [econstructor; eauto with uvalue].

    - (* InsertElement *)
      cbn in HX;
        repeat break_match_hyp_inv;
        invert_bools;
        unfold valid_ibinop_type in *;
        repeat break_match_hyp_inv;
        repeat match goal with
          | H: dtyp_eqb _ _ = true |- _ =>
              apply dtyp_eqb_eq in H; subst
          end;
        repeat match goal with
          | [ H1 : (forall dt, uvalue_has_dtyp_fun ?UV dt = true -> _),
                H2 : uvalue_has_dtyp_fun ?UV _ = true |- _] => apply H1 in H2
          end.

      all: try solve [econstructor; eauto with uvalue].


    - (* ShuffleVector *)
      cbn in HX;
        repeat break_match_hyp_inv;
        invert_bools;
        unfold valid_ibinop_type in *;
        repeat break_match_hyp_inv;
        repeat match goal with
          | H: dtyp_eqb _ _ = true |- _ =>
              apply dtyp_eqb_eq in H; subst
          end;
        repeat match goal with
          | [ H1 : (forall dt, uvalue_has_dtyp_fun ?UV dt = true -> _),
                H2 : uvalue_has_dtyp_fun ?UV _ = true |- _] => apply H1 in H2
          end.

      constructor; auto with uvalue.
      
      all: try solve [econstructor; eauto with uvalue].

    - (* ShuffleVector *)
      cbn in HX;
        repeat break_match_hyp_inv;
        invert_bools;
        unfold valid_ibinop_type in *;
        repeat break_match_hyp_inv;
        repeat match goal with
          | H: dtyp_eqb _ _ = true |- _ =>
              apply dtyp_eqb_eq in H; subst
          end;
        repeat match goal with
          | [ H1 : (forall dt, uvalue_has_dtyp_fun ?UV dt = true -> _),
                H2 : uvalue_has_dtyp_fun ?UV _ = true |- _] => apply H1 in H2
          end.

      constructor; eauto with uvalue.
      apply check_fetch_extract_path; auto.

    - (* InsertValue *)
      cbn in HX;
        repeat break_match_hyp_inv;
        invert_bools;
        unfold valid_ibinop_type in *;
        repeat break_match_hyp_inv;
        repeat match goal with
          | H: dtyp_eqb _ _ = true |- _ =>
              apply dtyp_eqb_eq in H; subst
          end;
        repeat match goal with
          | [ H1 : (forall dt, uvalue_has_dtyp_fun ?UV dt = true -> _),
                H2 : uvalue_has_dtyp_fun ?UV _ = true |- _] => apply H1 in H2
          end.

      constructor; auto with uvalue.

    - (* ConcatBytes *)
      cbn in HX;
        repeat break_match_hyp_inv;
        invert_bools;
        repeat match goal with
          | [ H1 : (forall dt, uvalue_has_dtyp_fun ?UV dt = true -> _),
                H2 : uvalue_has_dtyp_fun ?UV _ = true |- _] => apply H1 in H2; clear H1
          end.
      econstructor; eauto.
      intros byte HIN.
      rewrite forallb_forall in H1.
      specialize (H1 _ HIN).
      repeat break_match_hyp_inv.
      do 4 eexists. reflexivity.
      apply N.eqb_eq in H0; auto.
      
      Unshelve.
      all : exact (1%positive).
  Qed.

  Lemma uvalue_has_dtyp_fun_complete :
    forall uv dt,
      uvalue_has_dtyp uv dt -> uvalue_has_dtyp_fun uv dt = true.
  Proof using.
    intros uv dt TYPE.
    induction TYPE; auto;
      try solve [
          unfold uvalue_has_dtyp_fun;
          cbn;
          repeat break_inner_match_goal;
          solve
            [ apply dtyp_eqb_refl
            | contradiction
            ]
        | cbn; induction H; forward_bools; auto
        | cbn; repeat break_match_goal; auto; try contradiction;
          forward_bools; [rewrite forallb_forall; auto | apply Nat.eqb_eq; auto]
        | cbn; repeat break_match_goal; auto
        | cbn;
          repeat break_match_goal; invert_hyps; subst;
          try (inversion H0; subst; try contradiction);
          try (solve [inversion H]);
          forward_bools; auto
        ].

    - unfold uvalue_has_dtyp_fun.
      induction H; cbn; auto.
      + break_match_hyp_inv.
        cbn in *.
        break_inner_match_hyp; try discriminate.
        inv Heqs.
        unfold uvalue_has_dtyp_fun in H.
        break_match_hyp_inv.
        rewrite H2.
        apply dtyp_eqb_eq in H3, H2; subst.
        inv H2.
        apply dtyp_eqb_refl.
    - unfold uvalue_has_dtyp_fun.
      induction H; cbn; auto.
      + break_match_hyp_inv.
        cbn in *.
        break_inner_match_hyp; try discriminate.
        inv Heqs.
        unfold uvalue_has_dtyp_fun in H.
        break_match_hyp_inv.
        rewrite H2.
        apply dtyp_eqb_eq in H3, H2; subst.
        inv H2.
        apply dtyp_eqb_refl.
    - unfold uvalue_has_dtyp_fun.
      cbn.
      break_inner_match; try contradiction.
      apply forallb_forall in IH.
      setoid_rewrite IH.
      rewrite H0.
      rewrite Nnat.N2Nat.id.
      rewrite N.eqb_refl.
      cbn.
      apply dtyp_eqb_refl.
    - unfold uvalue_has_dtyp_fun.
      cbn.
      break_inner_match; try contradiction.
      apply forallb_forall in IH.
      setoid_rewrite IH.
      rewrite H0.
      rewrite Nnat.N2Nat.id.
      rewrite N.eqb_refl.
      cbn.
      break_inner_match; try contradiction.
      apply dtyp_eqb_refl.
    - invert_hyps; subst; cbn;
        unfold uvalue_has_dtyp_fun in *; cbn;
        repeat break_match_hyp_inv;
        repeat match goal with
          | H: dtyp_eqb _ _ = true |- _ =>
              apply dtyp_eqb_eq in H; subst
          end;
        try setoid_rewrite dtyp_eqb_refl;
        cbn; auto;
        apply dtyp_eqb_refl.
    - invert_hyps; subst; cbn;
        unfold uvalue_has_dtyp_fun in *; cbn;
        repeat break_match_hyp_inv;
        repeat match goal with
          | H: dtyp_eqb _ _ = true |- _ =>
              apply dtyp_eqb_eq in H; subst
          end;
        try setoid_rewrite dtyp_eqb_refl;
        cbn; auto;
        apply dtyp_eqb_refl.
    - destruct H as [[HX HY] | [[HX HY] | [HX HY]]];
        try solve [unfold uvalue_has_dtyp_fun in *; cbn in *;
        repeat break_match_hyp_inv;
        repeat match goal with
          | H: dtyp_eqb _ _ = true |- _ =>
              apply dtyp_eqb_eq in H; subst
          end;
        try setoid_rewrite dtyp_eqb_refl;
        cbn; auto].
    - destruct H as [[HX HY] | [[HX HY] | [HX HY]]];
      try solve [unfold uvalue_has_dtyp_fun in *; cbn in *;
        repeat break_match_hyp_inv;
        repeat match goal with
          | H: dtyp_eqb _ _ = true |- _ =>
              apply dtyp_eqb_eq in H; subst
          end;
        try setoid_rewrite dtyp_eqb_refl;
        cbn; auto; apply dtyp_eqb_refl].

    - invert_hyps; subst; cbn;
        unfold uvalue_has_dtyp_fun in *; cbn;
        repeat break_match_hyp_inv;
        repeat match goal with
          | H: dtyp_eqb _ _ = true |- _ =>
              apply dtyp_eqb_eq in H; subst
          end;
        try setoid_rewrite dtyp_eqb_refl;
        cbn; auto;
        apply dtyp_eqb_refl.
    - invert_hyps; subst; cbn;
        unfold uvalue_has_dtyp_fun in *; cbn;
        repeat break_match_hyp_inv;
        repeat match goal with
          | H: dtyp_eqb _ _ = true |- _ =>
              apply dtyp_eqb_eq in H; subst
          end;
        try setoid_rewrite dtyp_eqb_refl;
        cbn; auto;
        apply dtyp_eqb_refl.
    - destruct H as [H | H]; subst;
        try solve [unfold uvalue_has_dtyp_fun in *; cbn in *;
        repeat break_match_hyp_inv;
        repeat match goal with
          | H: dtyp_eqb _ _ = true |- _ =>
              apply dtyp_eqb_eq in H; subst
          end;
        try setoid_rewrite dtyp_eqb_refl;
        cbn; auto].
    - destruct H as [H | H]; subst;
      try solve [unfold uvalue_has_dtyp_fun in *; cbn in *;
        repeat break_match_hyp_inv;
        repeat match goal with
          | H: dtyp_eqb _ _ = true |- _ =>
              apply dtyp_eqb_eq in H; subst
          end;
        try setoid_rewrite dtyp_eqb_refl;
        cbn; auto; apply dtyp_eqb_refl].
    - unfold uvalue_has_dtyp_fun in *; cbn in *;
        repeat break_match_hyp_inv;
        repeat match goal with
          | H: dtyp_eqb _ _ = true |- _ =>
              apply dtyp_eqb_eq in H; subst
          end;
        try setoid_rewrite dtyp_eqb_refl.
        cbn; rewrite H; cbn; auto; apply dtyp_eqb_refl.
    - unfold uvalue_has_dtyp_fun in *; cbn in *;
        repeat break_match_hyp_inv;
        repeat match goal with
          | H: dtyp_eqb _ _ = true |- _ =>
              apply dtyp_eqb_eq in H; subst
          end;
        try setoid_rewrite dtyp_eqb_refl; auto;
        destruct (N.eq_dec n n); try contradiction; subst;
        destruct (dtyp_eq_dec t t); subst; try contradiction;
        apply dtyp_eqb_refl.
    - unfold uvalue_has_dtyp_fun in *; cbn in *;
        repeat break_match_hyp_inv;
        repeat match goal with
          | H: dtyp_eqb _ _ = true |- _ =>
              apply dtyp_eqb_eq in H; subst
          end;
        try setoid_rewrite dtyp_eqb_refl; auto;
        cbn; apply dtyp_eqb_refl.
    - unfold uvalue_has_dtyp_fun in *; cbn in *;
        repeat break_match_hyp_inv;
        repeat match goal with
          | H: dtyp_eqb _ _ = true |- _ =>
              apply dtyp_eqb_eq in H; subst
          end;
        try setoid_rewrite dtyp_eqb_refl; auto;
        cbn; apply dtyp_eqb_refl.
    - unfold uvalue_has_dtyp_fun in *; cbn in *;
        repeat break_match_hyp_inv;
        repeat match goal with
          | H: dtyp_eqb _ _ = true |- _ =>
              apply dtyp_eqb_eq in H; subst
          end;
        try setoid_rewrite dtyp_eqb_refl; auto; cbn;
        destruct (dtyp_eq_dec d d); subst; try contradiction.
      unfold check_extract_path in H.
      break_match_hyp_inv.
      apply dtyp_eqb_eq in H1; subst; auto.
    - unfold uvalue_has_dtyp_fun in *; cbn in *;
        repeat break_match_hyp_inv;
        repeat match goal with
          | H: dtyp_eqb _ _ = true |- _ =>
              apply dtyp_eqb_eq in H; subst
          end;
        try setoid_rewrite dtyp_eqb_refl; auto; cbn.
      rewrite H.
      apply dtyp_eqb_refl.
    - unfold uvalue_has_dtyp_fun in *; cbn in *;
        repeat break_match_hyp_inv;
        repeat match goal with
          | H: dtyp_eqb _ _ = true |- _ =>
              apply dtyp_eqb_eq in H; subst
          end;
        try setoid_rewrite dtyp_eqb_refl; auto; cbn.
      destruct (dtyp_eq_dec d d); subst; try contradiction.
      apply dtyp_eqb_refl.
    - unfold uvalue_has_dtyp_fun in *; cbn in *;
        repeat break_match_hyp_inv;
        repeat match goal with
          | H: dtyp_eqb _ _ = true |- _ =>
              apply dtyp_eqb_eq in H; subst
          end;
        try setoid_rewrite dtyp_eqb_refl; auto; cbn.
      destruct (N.eq_dec sz sz); subst; try contradiction.
      destruct (dtyp_eq_dec t t); subst; try contradiction.
      apply dtyp_eqb_refl.
    - unfold uvalue_has_dtyp_fun in *; cbn in *;
        repeat break_match_hyp_inv;
        repeat match goal with
          | H: dtyp_eqb _ _ = true |- _ =>
              apply dtyp_eqb_eq in H; subst
          end;
        try setoid_rewrite dtyp_eqb_refl; auto; cbn.
      rewrite H0.
      rewrite N.eqb_refl.
      cbn.

      assert
        (forallb
           (fun byte : uvalue => match byte with
                              | UVALUE_ExtractByte _ _ _ _ => true
                              | _ => false
                              end) bytes = true).
      { apply forallb_forall.
        intros x H1.
        apply H in H1.
        destruct H1 as (?&?&?&?&?); subst; auto.
      }
      rewrite H1.
      apply dtyp_eqb_refl.
  Qed.

  Lemma uvalue_has_dtyp_fun_sound :
    forall uv dt,
      uvalue_has_dtyp_fun uv dt = true -> uvalue_has_dtyp uv dt.
  Proof using.
    intros uv dt H.
    unfold uvalue_has_dtyp_fun in H.
    break_match_hyp_inv.
    eapply dtyp_of_uvalue_fun_sound.
    apply dtyp_eqb_eq in H1; subst; auto.
  Qed.

  Lemma uvalue_has_dtyp_dec :
    forall uv dt,
      {uvalue_has_dtyp uv dt} + {~ uvalue_has_dtyp uv dt}.
  Proof using.
    intros.
    destruct (uvalue_has_dtyp_fun uv dt) eqn:H.
    left. apply uvalue_has_dtyp_fun_sound; auto.
    right. intros C. apply uvalue_has_dtyp_fun_complete in C.
    rewrite H in C. inversion C.
  Qed.

  Ltac solve_no_void_dec :=
    solve
      [ unfold Coqlib.proj_sumbool;
        break_match_goal; auto
      ].

  Ltac solve_dtyp_eqb :=
    solve
      [ apply dtyp_eqb_refl
      ].

  Ltac solve_dtyp_non_void_eqb :=
    solve
      [ unfold dtyp_non_void_eqb; red;
        apply andb_true_iff;
        split; [solve_no_void_dec | solve_dtyp_eqb]
      | solve_no_void
      ].

  Lemma uvalue_has_dtyp_struct_length :
    forall fields dts,
      uvalue_has_dtyp (UVALUE_Struct fields) (DTYPE_Struct dts) ->
      length fields = length dts.
  Proof using.
    intros fields dts H.
    inversion H; subst.
    clear H.
    induction H2; subst; auto.
    cbn. rewrite IHForall2; auto.
  Qed.

  Lemma uvalue_has_dtyp_packed_struct_length :
    forall fields dts,
      uvalue_has_dtyp (UVALUE_Packed_struct fields) (DTYPE_Packed_struct dts) ->
      length fields = length dts.
  Proof using.
    intros fields dts H.
    inversion H; subst.
    clear H.
    induction H2; subst; auto.
    cbn. rewrite IHForall2; auto.
  Qed.

  Lemma dvalue_has_dtyp_struct_length :
    forall fields dts,
      dvalue_has_dtyp (DVALUE_Struct fields) (DTYPE_Struct dts) ->
      length fields = length dts.
  Proof using.
    intros fields dts H.
    inversion H; subst.
    clear H.
    induction H2; subst; auto.
    cbn. rewrite IHForall2; auto.
  Qed.

  Lemma dvalue_has_dtyp_packed_struct_length :
    forall fields dts,
      dvalue_has_dtyp (DVALUE_Packed_struct fields) (DTYPE_Packed_struct dts) ->
      length fields = length dts.
  Proof using.
    intros fields dts H.
    inversion H; subst.
    clear H.
    induction H2; subst; auto.
    cbn. rewrite IHForall2; auto.
  Qed.


  (** Tactics... Maybe move these *)
  Ltac normalize_array_vector_dtyp :=
    match goal with
    | H : _ |- dvalue_has_dtyp _ (DTYPE_Array (BinNat.N.of_nat) _) =>
        idtac
    | H : _ |- dvalue_has_dtyp _ (DTYPE_Array ?sz _) =>
        rewrite <- (Nnat.N2Nat.id sz)
    | H : _ |- dvalue_has_dtyp _ (DTYPE_Vector (BinNat.N.of_nat) _) =>
        idtac
    | H : _ |- dvalue_has_dtyp _ (DTYPE_Vector ?sz _) =>
        rewrite <- (Nnat.N2Nat.id sz)
    end.

  #[global] Hint Resolve forall_repeat_true : DVALUE_HAS_DTYP.
  #[global] Hint Constructors dvalue_has_dtyp : DVALUE_HAS_DTYP.
  #[global] Hint Rewrite Nnat.Nat2N.id : DVALUE_HAS_DTYP.
  #[global] Hint Resolve List.repeat_length : DVALUE_HAS_DTYP.
  #[global] Hint Extern 1 (NO_VOID _) => solve_no_void : DVALUE_HAS_DTYP.

  Ltac solve_dvalue_has_dtyp :=
    try normalize_array_vector_dtyp;
    solve [autorewrite with DVALUE_HAS_DTYP; auto with DVALUE_HAS_DTYP].

  #[global] Hint Resolve forall_repeat_true : UVALUE_HAS_DTYP.
  #[global] Hint Constructors uvalue_has_dtyp : UVALUE_HAS_DTYP.
  #[global] Hint Rewrite Nnat.Nat2N.id : UVALUE_HAS_DTYP.
  #[global] Hint Resolve List.repeat_length : UVALUE_HAS_DTYP.
  #[global] Hint Extern 1 (NO_VOID _) => solve_no_void : UVALUE_HAS_DTYP.

  Ltac solve_uvalue_has_dtyp :=
    try normalize_array_vector_dtyp;
    solve [autorewrite with UVALUE_HAS_DTYP; auto with UVALUE_HAS_DTYP].


  Section EvalIopLemmas.
    Context (M : Type -> Type).
    Context {Eq1 : @Monad.Eq1 M}.
    Context {Monad : Monad M}.
    Context {MonadLaws : Monad.MonadLawsE M}.
    Context {RET_INV : @Eq1_ret_inv M Eq1 Monad}.
    Context {Eq1EQV : @Monad.Eq1Equivalence M Monad Eq1}.
    Context {RETS : @MonadReturns M Monad Eq1}.
    Context {NFR : @NoFailsRet M Monad Eq1 RETS}.
    Context {MFR : @MonadReturnsFails M Monad Eq1 RETS}.
    Context {ERR : RAISE_ERROR M}.
    Context {UB : RAISE_UB M}.
    Context {OOM : RAISE_OOM M}.
    Context {FERR : MFails_ERROR M}.
    Context {FUB : MFails_UB M}.
    Context {FOOM : MFails_OOM M}.

    Lemma eval_iop_integer_h_dtyp :
      forall dx dy dv sz op,
        dvalue_has_dtyp dx (DTYPE_I sz) ->
        dvalue_has_dtyp dy (DTYPE_I sz) ->
        Monad.eq1 (eval_iop_integer_h op dx dy) (@ret M _ _ dv) ->
        dvalue_has_dtyp dv (DTYPE_I sz).
    Proof using ERR Eq1 FERR FUB M Monad NFR OOM RETS RET_INV UB.
      intros dx dy dv sz op TYPx TYPy EVAL.
      inversion TYPx; inversion TYPy; subst; cbn in EVAL;
        try solve [
            cbn in *;
            destruct op; cbn in EVAL;
              repeat break_match_hyp;
              try solve
                [first
                   [ apply eq1_ret_ret in EVAL; [| solve [eauto]]
                   | apply MReturns_ret in EVAL;
                     apply MReturns_bind_inv in EVAL as [FAILS | (res & MA & RET)];
                     [ cbn in FAILS; apply MFails_ret in FAILS; contradiction
                     | break_match_hyp; apply MReturns_ret_inv in RET
                     ]
                   | apply MReturns_ret in EVAL;
                     apply MReturns_bind_inv in EVAL as [FAILS | (res & MA & RET)];
                     [ cbn in FAILS; apply MFails_ret in FAILS; contradiction
                     | repeat break_match_hyp;
                       [ apply MReturns_ret_inv in RET
                       | cbn in RET;
                         apply MReturns_bind_inv in RET as [FAILS | (res' & MA' & RET)];
                         [ cbn in FAILS; apply MFails_ret in FAILS; contradiction
                         | repeat break_match_hyp;
                           apply MReturns_ret_inv in RET
                         ]
                       ]
                     ]
                   ]; subst; solve_dvalue_has_dtyp];
              try solve [eapply EqRet_NoFail in EVAL; eauto;
                         exfalso; apply EVAL;
                         first [apply mfails_ub | apply mfails_error | apply mfails_oom]; eauto];

            try solve [apply MReturns_ret in EVAL;
              apply MReturns_bind_inv in EVAL as [FAILS | (res & MA & RET)];
              [ cbn in FAILS; apply MFails_ret in FAILS; contradiction |];
                       apply MReturns_ret_inv in RET; subst; constructor
              ]; constructor
          ].
      - break_match_hyp; try contradiction.
        dependent destruction e.
        cbn in *.
        destruct op; cbn in EVAL;
          repeat break_match_hyp;
          try solve
            [first
               [ apply eq1_ret_ret in EVAL; [| solve [eauto]]
               | apply MReturns_ret in EVAL;
                 apply MReturns_bind_inv in EVAL as [FAILS | (res & MA & RET)];
                 [ cbn in FAILS; apply MFails_ret in FAILS; contradiction
                 | break_match_hyp; apply MReturns_ret_inv in RET
                 ]
               | apply MReturns_ret in EVAL;
                 apply MReturns_bind_inv in EVAL as [FAILS | (res & MA & RET)];
                 [ cbn in FAILS; apply MFails_ret in FAILS; contradiction
                 | repeat break_match_hyp;
                   [ apply MReturns_ret_inv in RET
                   | cbn in RET;
                     apply MReturns_bind_inv in RET as [FAILS | (res' & MA' & RET)];
                     [ cbn in FAILS; apply MFails_ret in FAILS; contradiction
                     | repeat break_match_hyp;
                       apply MReturns_ret_inv in RET
                     ]
                   ]
                 ]
               ]; subst; solve_dvalue_has_dtyp].

      all:
        try solve [eapply EqRet_NoFail in EVAL; eauto;
        exfalso; apply EVAL;
        first [apply mfails_ub | apply mfails_error | apply mfails_oom]; eauto].

      all : apply MReturns_ret in EVAL;
              apply MReturns_bind_inv in EVAL as [FAILS | (res & MA & RET)];
                          [ cbn in FAILS; apply MFails_ret in FAILS; contradiction |];
                          apply MReturns_ret_inv in RET; subst; constructor.
      all : constructor.
    Qed.

    Lemma eval_iop_dtyp_i :
      forall dx dy dv sz op,
        dvalue_has_dtyp dx (DTYPE_I sz) ->
        dvalue_has_dtyp dy (DTYPE_I sz) ->
        Monad.eq1 (eval_iop op dx dy) (ret dv) ->
        dvalue_has_dtyp dv (DTYPE_I sz).
    Proof using ERR Eq1 FERR FUB M Monad NFR OOM RETS RET_INV UB.
      intros dx dy dv sz op TYPx TYPy EVAL.
      unfold eval_iop in EVAL.
      inversion TYPx; inversion TYPy; subst; try lia.
      all: eapply eval_iop_integer_h_dtyp in EVAL; eauto.
    Qed.

    Lemma eval_iop_integer_h_dtyp_iptr :
      forall dx dy dv op,
        dvalue_has_dtyp dx DTYPE_IPTR ->
        dvalue_has_dtyp dy DTYPE_IPTR ->
        Monad.eq1 (eval_iop_integer_h op dx dy) (ret dv) ->
        dvalue_has_dtyp dv DTYPE_IPTR.
    Proof using ERR Eq1 FERR FOOM FUB M MFR Monad NFR OOM RETS RET_INV UB.
      intros dx dy dv op TYPx TYPy EVAL.
      inversion TYPx; inversion TYPy; subst;
        destruct op;
        cbn in EVAL;
        repeat break_match_hyp;
        pose proof EVAL as CONTRA;
        try solve
          [first [ apply eq1_ret_ret in EVAL;
                   subst;
                   [ try (unfold VMemInt_intptr';
                          repeat rewrite VMemInt_intptr_dtyp in *)
                         | solve [eauto]
                       ]

                   | eapply EqRet_NoFail in CONTRA; eauto;
                     exfalso; apply CONTRA;
                     apply mfails_ub; eauto

                   | eapply EqRet_NoFail in CONTRA; eauto;
                     exfalso; apply CONTRA;
                     apply mfails_error; eauto

                   | apply MReturns_ret in EVAL;
                     apply MReturns_bind_inv in EVAL as [FAILS | (res & MA & RET)];
                     [eapply EqRet_NoFail in CONTRA; eauto;
                      exfalso; apply CONTRA;
                      apply MFails_bind_ma; eauto
                     | first
                         [ apply MReturns_ret_inv in RET;
                           cbn in RET
                         | break_match_hyp;
                           [ apply MFails_MReturns in RET; try contradiction;
                             apply mfails_oom; eauto
                           | apply MReturns_ret_inv in RET;
                             cbn in RET
                           ]
                         ]
                     ]

                   | apply MReturns_ret in EVAL;
                     apply MReturns_bind_inv in EVAL as [FAILS | (res & MA & RET)];
                     [eapply EqRet_NoFail in CONTRA; eauto;
                      exfalso; apply CONTRA;
                      apply MFails_bind_ma; eauto
                     | first
                         [ apply MReturns_ret_inv in RET;
                           cbn in RET
                         | break_match_hyp;
                           [ apply MFails_MReturns in RET; try contradiction;
                             apply mfails_oom; eauto
                           | apply MReturns_ret_inv in RET;
                             cbn in RET
                           ]
                         ]
                     ]

                   | apply MReturns_ret in EVAL;
                     apply MReturns_bind_inv in EVAL as [FAILS | (res & MA & RET)];
                     [ eapply EqRet_NoFail in CONTRA; eauto;
                       exfalso; apply CONTRA;
                       apply MFails_bind_ma; eauto
                     | clear CONTRA;
                       break_match_hyp;
                       first
                         [ apply MReturns_ret_inv in RET;
                           cbn in RET
                         | break_match_hyp;
                           [ apply MFails_MReturns in RET; try contradiction;
                             apply mfails_oom; eauto
                           | apply MReturns_ret_inv in RET;
                             cbn in RET
                           ]
                         ]
                     ]

                   | apply MReturns_ret in EVAL;
                     apply MReturns_bind_inv in EVAL as [FAILS | (res & MA & RET)];
                     [ eapply EqRet_NoFail in CONTRA; eauto;
                       exfalso; apply CONTRA;
                       apply MFails_bind_ma; eauto
                     | repeat match goal with
                         | H : MReturns _ (if ?c then _ else _) |- _ =>
                             destruct c eqn:?
                         end;
                       try solve [ apply MFails_MReturns in RET; try contradiction;
                                   apply mfails_oom; eauto
                                 | apply MReturns_ret_inv in RET;
                                   cbn in RET
                         ];
                       try (apply MReturns_bind_inv in RET as [FAILS | (res' & MA' & RET)];
                            [eapply EqRet_NoFail in CONTRA; eauto;
                             exfalso; apply CONTRA;
                             eapply MFails_bind_k; eauto;
                             break_match;
                             [ match goal with
                               | H: true = false |- _ =>
                                   inversion H
                               end
                             |]; eapply MFails_bind_ma; eauto
                            |]
                         );
                       try (match goal with
                            | H : MReturns _ (if ?c then _ else _) |- _ =>
                                destruct c eqn:?
                            end);
                       try solve [ apply MFails_MReturns in RET; try contradiction;
                                   apply mfails_oom; eauto
                                 | apply MReturns_ret_inv in RET;
                                   cbn in RET
                         ];
                       apply MReturns_ret_inv in RET; cbn in RET
                     ]
                   ]; subst;
                   try (unfold VMemInt_intptr';
                        rewrite VMemInt_intptr_dtyp);
                   solve_dvalue_has_dtyp].
    Qed.

    Lemma eval_iop_dtyp_iptr :
      forall dx dy dv op,
        dvalue_has_dtyp dx DTYPE_IPTR ->
        dvalue_has_dtyp dy DTYPE_IPTR ->
        Monad.eq1 (eval_iop op dx dy) (ret dv) ->
        dvalue_has_dtyp dv DTYPE_IPTR.
    Proof using ERR Eq1 FERR FOOM FUB M MFR Monad NFR OOM RETS RET_INV UB.
      intros dx dy dv op TYPx TYPy EVAL.
      unfold eval_iop in EVAL.
      inversion TYPx; inversion TYPy; subst; try lia.
      all: eapply eval_iop_integer_h_dtyp_iptr in EVAL; eauto.
    Qed.
  End EvalIopLemmas.

  Definition default_dvalue_of_dtyp_i (sz : positive) : dvalue :=
    @DVALUE_I sz (repr 0).

  (* Handler for PickE which concretizes everything to 0 *)
  (* If this succeeds the dvalue returned should agree with
     dvalue_has_dtyp for the sake of the dvalue_default lemma. *)
  Fixpoint default_dvalue_of_dtyp (dt : dtyp) : err dvalue :=
    match dt with
    | DTYPE_I sz => ret (default_dvalue_of_dtyp_i sz)
    | DTYPE_IPTR => ret (DVALUE_IPTR IP.zero)
    | DTYPE_Pointer => ret (DVALUE_Addr A.null)
    | DTYPE_Void => failwith "DTYPE_Void is not a true LLVM value"
    | DTYPE_Half => failwith "Unimplemented default type: half"
    | DTYPE_Float => ret (DVALUE_Float Float32.zero)
    | DTYPE_Double => ret (DVALUE_Double (Float32.to_double Float32.zero))
    | DTYPE_X86_fp80 => failwith "Unimplemented default type: x86_fp80"
    | DTYPE_Fp128 => failwith "Unimplemented default type: fp128"
    | DTYPE_Ppc_fp128 => failwith "Unimplemented default type: ppc_fp128"
    | DTYPE_Metadata => failwith "Unimplemented default type: metadata"
    | DTYPE_X86_mmx => failwith "Unimplemented default type: x86_mmx"
    | DTYPE_Opaque => failwith "Unimplemented default type: opaque"
    | DTYPE_Array sz t =>
        v <- default_dvalue_of_dtyp t ;;
        (ret (DVALUE_Array dt (repeat v (N.to_nat sz))))

    (* Matching valid Vector types... *)
    (* Currently commented out unsupported ones *)
    (* | DTYPE_Vector sz (DTYPE_Half) => *)
    (*   if (0 <=? sz) then *)
    (*     (ret (DVALUE_Vector *)
    (*             (repeat (DVALUE_Float Float32.zero) (N.to_nat sz)))) *)
    (*   else *)
    (*     failwith ("Negative array length for generating default value" ++ *)
    (*     "of DTYPE_Array or DTYPE_Vector") *)
    | DTYPE_Vector sz (DTYPE_Float) =>
        ret (DVALUE_Vector dt
               (repeat (DVALUE_Float Float32.zero) (N.to_nat sz)))
    | DTYPE_Vector sz (DTYPE_Double) =>
        ret (DVALUE_Vector dt
               (repeat (DVALUE_Double (Float32.to_double Float32.zero))
                       (N.to_nat sz)))
    (* | DTYPE_Vector sz (DTYPE_X86_fp80) => *)
    (*   if (0 <=? sz) then *)
    (*     (ret (DVALUE_Vector *)
    (*             (repeat (DVALUE_Float Float32.zero) (N.to_nat sz)))) *)
    (*   else *)
    (*     failwith ("Negative array length for generating default value" ++ *)
    (*     "of DTYPE_Array or DTYPE_Vector") *)
    (* | DTYPE_Vector sz (DTYPE_Fp128) => *)
    (*   if (0 <=? sz) then *)
    (*     (ret (DVALUE_Vector *)
    (*             (repeat (DVALUE_Float Float32.zero) (N.to_nat sz)))) *)
    (*   else *)
    (*     failwith ("Negative array length for generating default value" ++ *)
    (*     "of DTYPE_Array or DTYPE_Vector") *)
    | DTYPE_Vector sz (DTYPE_I n) =>
        let v := default_dvalue_of_dtyp_i n in
        ret (DVALUE_Vector dt (repeat v (N.to_nat sz)))

    | DTYPE_Vector sz DTYPE_Pointer =>
        ret (DVALUE_Vector dt (repeat (DVALUE_Addr A.null) (N.to_nat sz)))

    | DTYPE_Vector sz DTYPE_IPTR =>
        ret (DVALUE_Vector dt (repeat (DVALUE_IPTR zero) (N.to_nat sz)))

    | DTYPE_Vector _ _ => failwith ("Non-valid or unsupported vector type when generating default vector")
    | DTYPE_Struct fields =>
        v <- @map_monad err _ dtyp dvalue default_dvalue_of_dtyp fields;;
        ret (DVALUE_Struct v)
    | DTYPE_Packed_struct fields =>
        v <- @map_monad err _ dtyp dvalue default_dvalue_of_dtyp fields;;
        ret (DVALUE_Packed_struct v)
    end.

  Ltac do_it := constructor; cbn; auto; fail.

  Lemma dvalue_default_NO_VOID :
    forall t v, (default_dvalue_of_dtyp t) = inr v -> NO_VOID t.
  Proof using.
    induction t; intros; cbn; auto.
    - inversion H.

    - cbn in H.
      repeat break_match_hyp_inv; auto.
      eapply IHt; eauto.
    - cbn in *.
      break_match_hyp_inv.
      rewrite FORALL_forall.
      rewrite Forall_forall.
      intros.
      specialize (@map_monad_err_In' err _ _ _ _ _ _ _ _ _ _ default_dvalue_of_dtyp fields l _ H0 Heqs) as HX.
      destruct HX as [b [EQ _]].
      eapply H; eauto.
    - cbn in *.
      break_match_hyp_inv.
      rewrite FORALL_forall.
      rewrite Forall_forall.
      intros.
      specialize (@map_monad_err_In' err _ _ _ _ _ _ _ _ _ _ default_dvalue_of_dtyp fields l _ H0 Heqs) as HX.
      destruct HX as [b [EQ _]].
      eapply H; eauto.
    - cbn in H.
      repeat break_match_hyp_inv; cbn; auto.
  Qed.

  Lemma dvalue_default : forall t v,
      (default_dvalue_of_dtyp t) = inr v ->
      dvalue_has_dtyp v t.
  Proof using.
    intros t v. revert v.
    induction t; try do_it;
      try (intros; subst; inversion H; constructor).
    - intros. subst. inversion H. clear H.
      break_match_hyp_inv.
      constructor.
      + eapply dvalue_default_NO_VOID. apply Heqs.
      + apply forall_repeat_true. eapply IHt. reflexivity.
      + rewrite repeat_length. reflexivity.
    - intros.
      cbn in H0.
      repeat break_match_hyp_inv.
      constructor.
      apply map_monad_err_Forall2 in Heqs.
      (* could be prettier *)
      induction Heqs; auto.
      constructor.
      eapply H; auto. left; reflexivity.
      eapply IHHeqs; auto.
      intros.
      eapply H. right; auto. assumption.
    - intros.
      cbn in H0.
      repeat break_match_hyp_inv.
      constructor.
      apply map_monad_err_Forall2 in Heqs.
      (* could be prettier *)
      induction Heqs; auto.
      constructor.
      eapply H; auto. left; reflexivity.
      eapply IHHeqs; auto.
      intros.
      eapply H. right; auto. assumption.
    - intros.
      cbn in H.
      repeat break_match_hyp_inv; cbn; constructor; cbn; auto;
        try solve [
            apply forall_repeat_true;eapply IHt; eauto
          | rewrite repeat_length; auto
          | unfold vector_dtyp; intuition auto with *
          ].
      + unfold vector_dtyp.
        left. exists sz0; auto.
  Qed.

  Definition uvalue_constructor_string (u : uvalue) : string
    := match u with
       | UVALUE_Addr a => "UVALUE_Addr"
       | @UVALUE_I sz x => "UVALUE_I1"
       | UVALUE_IPTR x => "UVALUE_IPTR"
       | UVALUE_Double x => "UVALUE_Double"
       | UVALUE_Float x => "UVALUE_Float"
       | UVALUE_Undef t => "UVALUE_Undef"
       | UVALUE_Poison t => "UVALUE_Poison"
       | UVALUE_Oom t => "UVALUE_Oom"
       | UVALUE_None => "UVALUE_None"
       | UVALUE_Struct fields => "UVALUE_Struct"
       | UVALUE_Packed_struct fields => "UVALUE_Packed_struct"
       | UVALUE_Array t elts => "UVALUE_Array"
       | UVALUE_Vector t elts => "UVALUE_Vector"
       | UVALUE_IBinop iop v1 v2 => "UVALUE_IBinop"
       | UVALUE_ICmp cmp v1 v2 => "UVALUE_ICmp"
       | UVALUE_FBinop fop fm v1 v2 => "UVALUE_FBinop"
       | UVALUE_FCmp cmp v1 v2 => "UVALUE_FCmp"
       | UVALUE_Conversion conv t_from v t_to => "UVALUE_Conversion"
       | UVALUE_GetElementPtr t ptrval idxs => "UVALUE_GetElementPtr"
       | UVALUE_ExtractElement t vec idx => "UVALUE_ExtractElement"
       | UVALUE_InsertElement t vec elt idx => "UVALUE_InsertElement"
       | UVALUE_ShuffleVector t vec1 vec2 idxmask => "UVALUE_ShuffleVector"
       | UVALUE_ExtractValue t vec idxs => "UVALUE_ExtractValue"
       | UVALUE_InsertValue t vec u elt idxs => "UVALUE_InsertValue"
       | UVALUE_Select cnd v1 v2 => "UVALUE_Select"
       | UVALUE_ExtractByte uv dt idx sid => "UVALUE_ExtractByte"
       | UVALUE_ConcatBytes uvs dt => "UVALUE_ConcatBytes"
       end.

  Lemma dvalue_to_uvalue_preserves_dtyp :
    forall dv dt,
      dvalue_has_dtyp dv dt ->
      uvalue_has_dtyp (dvalue_to_uvalue dv) dt.
  Proof using.
    intros dv dt DT.
    induction DT;
      try solve [cbn; constructor; auto].
    - cbn.
      constructor.
      eapply Forall2_map_impl; eauto.
      auto.
    - cbn.
      constructor.
      eapply Forall2_map_impl; eauto.
      auto.
    - cbn.
      constructor; auto.
      + rewrite Forall_forall.
        intros.
        apply Coqlib.list_in_map_inv in H1.
        destruct H1 as [dv [EQ]].
        specialize (IH dv H1).
        subst.
        assumption.
      + rewrite map_length; auto.

    - constructor; auto.
      + rewrite Forall_forall.
        intros.
        apply Coqlib.list_in_map_inv in H2.
        destruct H2 as [dv [EQ]].
        specialize (IH dv H2).
        subst.
        assumption.
      + rewrite map_length; auto.
  Qed.

  Lemma uvalue_to_dvalue_preserves_dtyp :
    forall uv dv dt,
      uvalue_has_dtyp uv dt ->
      uvalue_to_dvalue uv = inr dv ->
      dvalue_has_dtyp dv dt.
  Proof using.
    intros uv dv dt UT; revert dv;
    induction UT; intros dv U2D;
      try solve
        [ cbn in U2D; inv U2D; cbn; solve_dvalue_has_dtyp ].

    - cbn in U2D.
      repeat break_match_hyp_inv.
      apply map_monad_err_Forall2 in Heqs.
      constructor.
      revert fts H.
      induction Heqs; intros; inversion H; auto.
      inversion H0; subst.
      constructor; auto.
    - cbn in U2D.
      repeat break_match_hyp_inv.
      apply map_monad_err_Forall2 in Heqs.
      constructor.
      revert fts H.
      induction Heqs; intros; inversion H; auto.
      inversion H0; subst.
      constructor; auto.
    - cbn in U2D.
      repeat break_match_hyp_inv.
      apply map_monad_err_Forall2 in Heqs.
      constructor; auto.
      + clear H0.
        induction Heqs; intros; auto.
        constructor.
        eapply IH; eauto. left; auto.
        apply IHHeqs.
        intros. eapply IH; eauto. right; auto.
      + apply Forall2_length in Heqs.
        rewrite <- Heqs. assumption.

    - cbn in U2D.
      repeat break_match_hyp_inv.
      apply map_monad_err_Forall2 in Heqs.
      constructor; auto.
      + clear H0.
        induction Heqs; intros; auto.
        constructor.
        eapply IH; eauto. left; auto.
        apply IHHeqs.
        intros. eapply IH; eauto. right; auto.
      + apply Forall2_length in Heqs.
        rewrite <- Heqs. assumption.
  Qed.

  Lemma dvalue_to_uvalue_inj :
    forall a b,
      dvalue_to_uvalue a = dvalue_to_uvalue b ->
      a = b.
  Proof using.
    intros a.
    induction a; intros b EQ;
      destruct b; cbn in EQ; inv EQ; auto.
    - apply map_inj in H1; subst; auto.
    - apply map_inj in H1; subst; auto.
    - apply map_inj in H2; subst; auto.
    - apply map_inj in H2; subst; auto.
  Qed.

End DVALUE.
