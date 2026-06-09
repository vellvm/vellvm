(* begin hide *)
From Stdlib Require Import
     Relations
     DecidableClass
     Program.Wf
     Numbers.HexadecimalString.

Import BinInt.

From Vellvm.Numeric Require Import
  Integers Floats.

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
     Semantics.Params
     Semantics.VellvmIntegers
     QC.ShowAST.

Import DList.

Require Import Stdlib.Program.Equality.

(* TODO: when/if we cut ties to QC, change this import *)
From QuickChick Require Import Show.
(* Import EqvNotation. *)
Import Logic.

Open Scope N_scope.
(* end hide *)

(** * Dynamic values
    Definition of the dynamic values manipulated by VIR.
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

(* SAZ - TODO make this into typeclasses the way we did with bitint? *)
Definition ll_float  := Floats.float32.
Definition ll_double := Floats.float.

(* Sizeof is needed for for ConcatBytes case *)
(* Module DVALUE (A : ADDRESS) (IP : INTPTR) (S : SIZEOF). *)
Section DValue.
  Context {Pa : Params}.

  (* The set of dynamic values manipulated by an LLVM program. *)
  Unset Elimination Schemes.
  Inductive dvalue : Set :=
  | DVALUE_Addr (a:addr)
  | DVALUE_I (sz : positive) (x:@bit_int sz)
  | DVALUE_IPTR (x:iptr)
(* TODO - this version | DVALUE_FP (fp:floating_point_variant) (x:@float_val fp) *)
  | DVALUE_Double (x:ll_double)
  | DVALUE_Float (x:ll_float)
  | DVALUE_Poison (t:dtyp)
  | DVALUE_None
  | DVALUE_Struct        (fields: list dvalue)
  | DVALUE_Packed_struct (fields: list dvalue)
  | DVALUE_Array         (t:dtyp) (elts: list dvalue)
  | DVALUE_Vector        (t:dtyp) (elts: list dvalue)
  .
  Set Elimination Schemes.

  Fixpoint dtyp_of_dvalue (v:dvalue) : EOB dtyp :=
    let list_dtyps :=
      fix go (uvs : list dvalue) : EOB (list dtyp) :=
        match uvs with
        | [] => ret []
        | v::tl =>
            dt <- dtyp_of_dvalue v;;
            dts <- go tl;;
            ret (dt :: dts)
        end
    in
    match v with
    | DVALUE_Addr a => ret DTYPE_Pointer
    | DVALUE_I sz x => ret (DTYPE_I sz)
    | DVALUE_IPTR x => ret DTYPE_IPTR
    | DVALUE_Double x => ret (DTYPE_FP FP_double)
    | DVALUE_Float x => ret (DTYPE_FP FP_float)
    | DVALUE_Poison t => ret t
    | DVALUE_None => ret DTYPE_Void
    | DVALUE_Struct fields =>
        dts <- list_dtyps fields;;
        ret (DTYPE_Struct dts)
    | DVALUE_Packed_struct fields =>
        dts <- list_dtyps fields;;
        ret (DTYPE_Packed_struct dts)
    | DVALUE_Array (DTYPE_Array sz t) elts =>
        if @NO_VOID_dec t
        then
          if forallb (fun e => match dtyp_of_dvalue e with
                            | raise_ret t' => dtyp_eqb t t'
                            | _ => false end) elts
             && N.eqb sz (N.of_nat (length elts))
          then ret (DTYPE_Array (N.of_nat (length elts)) t)
          else raise_error "dtyp_of_dvalue: mismatched element type in array"
        else raise_error "dtyp_of_dvalue: void in array type"
    | DVALUE_Vector (DTYPE_Vector sz t) elts =>
        if @NO_VOID_dec t
        then
          if forallb (fun e => match dtyp_of_dvalue e with
                            | raise_ret t' => dtyp_eqb t t'
                            | _ => false end) elts
             && N.eqb sz (N.of_nat (length elts))
          then
            if @vector_dtyp_dec t
            then ret (DTYPE_Vector (N.of_nat (length elts)) t)
            else raise_error "dtyp_of_dvalue: invalid element type for vector"
          else raise_error "dtyp_of_dvalue: mismatched element type in vector"
        else raise_error "dtyp_of_dvalue: void in vector type"
                         
    | _ => raise_error "dtyp_of_dvalue: missing case"
    end.

  Definition double_to_hex_string (f : float) : string
    := "0x" ++ NilEmpty.string_of_uint (N.to_hex_uint (Z.to_N (unsigned (Float.to_bits f)))).

  Definition float_to_hex_string (f : float32) : string
    := double_to_hex_string (Float32.to_double f).

  #[global] Instance showFloat : Show float
    := {| show := double_to_hex_string |}.

  #[global] Instance showFloat32 : Show float32
    := {| show := float_to_hex_string |}.
  
  Fixpoint show_dvalue (dv : dvalue) : string :=
    match dv with
    | DVALUE_Addr a => "addr " ++ show_addr a
    | DVALUE_I sz x => "i" ++ show (Zpos sz) ++ " " ++ show (unsigned x)
    | DVALUE_IPTR x => "intptr " ++ show (to_Z x)
    | DVALUE_Double x => "double " ++ show x
    | DVALUE_Float x => "float " ++ show x
    | DVALUE_Poison t => "poison[" ++ show_dtyp t ++ "]"
    | DVALUE_None => "none"
    | DVALUE_Struct fields => "{" ++ String.concat ", " (map show_dvalue fields) ++ "}"
    | DVALUE_Packed_struct fields => "<{" ++ String.concat ", " (map show_dvalue fields) ++ "}>"
    | DVALUE_Array _ elts => "["  ++ String.concat ", " (map show_dvalue elts) ++ "]"
    | DVALUE_Vector _ elts => "<"  ++ String.concat ", " (map show_dvalue elts) ++ ">"
    end.

  #[global] Instance showDValue : Show dvalue
   := {| show := show_dvalue |}.                                       

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
    Hypothesis IH_I             : forall sz (x : @bit_int sz), P (@DVALUE_I sz x).
    Hypothesis IH_IPTR          : forall x, P (DVALUE_IPTR x).
    Hypothesis IH_Double        : forall x, P (DVALUE_Double x).
    Hypothesis IH_Float         : forall x, P (DVALUE_Float x).
    Hypothesis IH_Poison        : forall t, P (DVALUE_Poison t).
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
  
  Fixpoint dvalue_measure (dv : dvalue) : nat :=
    match dv with
    | DVALUE_Addr a => 1
    | DVALUE_I sz x => 1
    | DVALUE_IPTR x => 1
    | DVALUE_Double x => 1
    | DVALUE_Float x => 1
    | DVALUE_Poison t => 1
    | DVALUE_None => 1
    | DVALUE_Struct fields => S (S (list_sum (map dvalue_measure fields)))
    | DVALUE_Packed_struct fields => S (S (list_sum (map dvalue_measure fields)))
    | DVALUE_Array t elts => S (S (list_sum (map dvalue_measure elts)))
    | DVALUE_Vector t elts => S (S (list_sum (map dvalue_measure elts)))
    end.

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
    Hypothesis IH_I             : forall sz (x : @bit_int sz), P (@DVALUE_I sz x).
    Hypothesis IH_IPTR           : forall x, P (DVALUE_IPTR x).
    Hypothesis IH_Double        : forall x, P (DVALUE_Double x).
    Hypothesis IH_Float         : forall x, P (DVALUE_Float x).
    Hypothesis IH_Poison        : forall t, P (DVALUE_Poison t).
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
                [ dependent induction H; eauto; inv H
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
                    repeat (forward IHSTRICT2; eauto);
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
                    repeat (forward IHSTRICT2; eauto);
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
      - intros s H'; dependent induction H'.
        + (* rt_step *)
          match goal with
          | H: dvalue_direct_subterm ?x _,
              IH : forall u : dvalue, In u _ -> forall s : dvalue, dvalue_subterm s u -> P s
                                                        |- P ?x => 
              inv H ;
              apply IH_Subterm; eauto;
              intros; eapply IH; eauto;
              apply clos_t_rt; eauto
          end.
        + (* rt_refl *)
          apply IH_Subterm;
            intros * STRICT;
            dependent induction STRICT.
          * (* t_step *)
            match goal with
            | H: dvalue_direct_subterm ?x _,
                IH : forall u : dvalue, In u _ -> forall s : dvalue, dvalue_subterm s u -> P s
                                                          |- P ?x =>
                inv H;
                eapply IH; eauto;
                apply rt_refl
            end.
          * (* t_trans *)
            clear IHSTRICT1.
            do 8 (forward IHSTRICT2; eauto).
            pose proof t_trans _ _ _ _ _ STRICT1 STRICT2 as STRICT3.
            eapply dvalue_strict_subterm_inv in STRICT3 as (s&DIRECT&SUB).
            inv DIRECT.
            match goal with
            | IH : forall u : dvalue, In u ?fields -> forall s : dvalue, dvalue_subterm s u -> P s
                                                              |- P ?x =>
               eapply IH; eauto
            end.
        + (* rt_trans *)
          match goal with
          | XY : clos_refl_trans dvalue dvalue_direct_subterm ?x ?y,
              YZ : clos_refl_trans dvalue dvalue_direct_subterm ?y ?z,
                IH : forall u : dvalue, In u _ -> forall s : dvalue, dvalue_subterm s u -> P s
                                                          |- _ =>
              pose proof rt_trans _ _ _ _ _ XY YZ as XZ;
              apply clos_rt_inv in XZ as [EQ | [w [R TRANS]]];
             [ subst; pose proof dvalue_subterm_antisymmetric XY YZ; subst; eapply IHH'2; eauto
                  | inv R; eapply IH; eauto
                  ] 
          end.

      - intros s H'.
        dependent induction H'.
        + (* rt_step *)
          match goal with
          | H: dvalue_direct_subterm ?x _,
            IH : forall u : dvalue, In u _ -> forall s : dvalue, dvalue_subterm s u -> P s |- P ?x =>
              inv H;
              apply IH_Subterm; eauto;
              intros; eapply IH; eauto;
              apply clos_t_rt; eauto
          end.
        + (* rt_refl *)
          apply IH_Subterm.
          intros * STRICT;
            dependent induction STRICT.
          * (* t_step *)
              match goal with
              | H: dvalue_direct_subterm ?x _,
                  IH : forall u : dvalue, In u _ -> forall s : dvalue, dvalue_subterm s u -> P s
                                                            |- P ?x =>
                  inv H;
                  eapply IH; eauto;
                  apply rt_refl
              end.
          * (* t_trans *)
            match goal with
            | IH : forall u : dvalue, In u ?fields -> forall s : dvalue, dvalue_subterm s u -> P s
                                                              |- P ?x =>
                clear IHSTRICT1;
                repeat (forward IHSTRICT2; auto);
                pose proof t_trans _ _ _ _ _ STRICT1 STRICT2 as STRICT3;
                eapply dvalue_strict_subterm_inv in STRICT3 as (s&DIRECT&SUB);
                inv DIRECT;
                eapply IH; eauto
            end.
        + (* rt_trans *)
          match goal with
          | XY : clos_refl_trans dvalue dvalue_direct_subterm ?x ?y,
              YZ : clos_refl_trans dvalue dvalue_direct_subterm ?y ?z,
                IH : forall u : dvalue, In u _ -> forall s : dvalue, dvalue_subterm s u -> P s
                                                          |- _ =>
              pose proof rt_trans _ _ _ _ _ XY YZ as XZ;
              apply clos_rt_inv in XZ as [EQ | [w [R TRANS]]];
              [ subst;
                pose proof dvalue_subterm_antisymmetric XY YZ; subst; eapply IHH'2; eauto
              | inv R; eapply IH; eauto
              ]
          end.
      - intros s H'.
        dependent induction H'.
        + (* rt_step *)
          match goal with
          | H: dvalue_direct_subterm ?x _,
              IH : forall u : dvalue, In u _ -> forall s : dvalue, dvalue_subterm s u -> P s
                                                        |- P ?x =>
              inv H;
              apply IH_Subterm; eauto;
              intros; eapply IH; eauto;
              apply clos_t_rt; eauto
          end.
        + (* rt_refl *)
          apply IH_Subterm.
          intros * STRICT;
            dependent induction STRICT.
          * (* t_step *)
              match goal with
              | H: dvalue_direct_subterm ?x _,
                  IH : forall u : dvalue, In u _ -> forall s : dvalue, dvalue_subterm s u -> P s
                                                            |- P ?x =>
                  inv H;
                  eapply IH; eauto;
                  apply rt_refl
              end.
          * (* t_trans *)
            match goal with
            | IH : forall u : dvalue, In u ?fields -> forall s : dvalue, dvalue_subterm s u -> P s
                                                              |- P ?x =>
                clear IHSTRICT1;
                do 8 (forward IHSTRICT2; eauto);
                pose proof t_trans _ _ _ _ _ STRICT1 STRICT2 as STRICT3;
                eapply dvalue_strict_subterm_inv in STRICT3 as (s&DIRECT&SUB);
                inv DIRECT;
                eapply IH; eauto
            end.
        + (* rt_trans *)
          match goal with
          | XY : clos_refl_trans dvalue dvalue_direct_subterm ?x ?y,
              YZ : clos_refl_trans dvalue dvalue_direct_subterm ?y ?z,
                IH : forall u : dvalue, In u _ -> forall s : dvalue, dvalue_subterm s u -> P s
                                                          |- _ =>
              pose proof rt_trans _ _ _ _ _ XY YZ as XZ;
              apply clos_rt_inv in XZ as [EQ | [w [R TRANS]]];
              [ subst;
                pose proof dvalue_subterm_antisymmetric XY YZ; subst; eapply IHH'2; eauto
              | inv R; eapply IH; eauto
              ]
          end.
       - intros s H'.
        dependent induction H'.
        + (* rt_step *)
          match goal with
          | H: dvalue_direct_subterm ?x _,
              IH : forall u : dvalue, In u _ -> forall s : dvalue, dvalue_subterm s u -> P s
                                                        |- P ?x =>
              inv H;
              apply IH_Subterm; eauto;
              intros; eapply IH; eauto;
              apply clos_t_rt; eauto
          end.
        + (* rt_refl *)
          apply IH_Subterm.
          intros * STRICT;
            dependent induction STRICT.
          * (* t_step *)
              match goal with
              | H: dvalue_direct_subterm ?x _,
                  IH : forall u : dvalue, In u _ -> forall s : dvalue, dvalue_subterm s u -> P s
                                                            |- P ?x =>
                  inv H;
                  eapply IH; eauto;
                  apply rt_refl
              end.
          * (* t_trans *)
            match goal with
            | IH : forall u : dvalue, In u ?fields -> forall s : dvalue, dvalue_subterm s u -> P s
                                                              |- P ?x =>
                clear IHSTRICT1;
                do 8 (forward IHSTRICT2; eauto);
                pose proof t_trans _ _ _ _ _ STRICT1 STRICT2 as STRICT3;
                eapply dvalue_strict_subterm_inv in STRICT3 as (s&DIRECT&SUB);
                inv DIRECT;
                eapply IH; eauto
            end.
        + (* rt_trans *)
          match goal with
          | XY : clos_refl_trans dvalue dvalue_direct_subterm ?x ?y,
              YZ : clos_refl_trans dvalue dvalue_direct_subterm ?y ?z,
                IH : forall u : dvalue, In u _ -> forall s : dvalue, dvalue_subterm s u -> P s
                                                          |- _ =>
              pose proof rt_trans _ _ _ _ _ XY YZ as XZ;
              apply clos_rt_inv in XZ as [EQ | [w [R TRANS]]];
              [ subst;
                pose proof dvalue_subterm_antisymmetric XY YZ; subst; eapply IHH'2; eauto
              | inv R; eapply IH; eauto
              ]
          end.
    Qed.
  End DvalueStrongInd.

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

  Definition dvalue_is_poison (dv : dvalue) : bool :=
    match dv with
    | DVALUE_Poison dt => true
    | _ => false
    end.

  Section DecidableEquality.

    Definition dvalue_int_eq_dec_helper
      (sz1 sz2 : positive) (x1 : @bit_int sz1) (x2 : @bit_int sz2) : {@DVALUE_I sz1 x1 = @DVALUE_I sz2 x2} + {@DVALUE_I sz1 x1 <> @DVALUE_I sz2 x2}.
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
          if eq_dec_addr a1 a2 then true else false
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

    Ltac dec_dvalue :=
      match goal with
      | [ |- { ?X ?a = ?X ?b} + { ?X ?a <> ?X ?b} ] => idtac
      | [ |- { ?X ?a = ?Y ?b} + { ?X ?a <> ?Y ?b} ] => right; intros H; inversion H
      | [ |- { ?X = ?X } + { ?X <> ?X } ] => left; reflexivity
      | [ |- { ?X = ?Y } + { ?X <> ?Y } ] => right; intros H; inversion H
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
      - destruct (eq_dec_addr a1 a2).
        * left; subst; reflexivity.
        * right; intros H; inversion H. contradiction.
      - apply dvalue_int_eq_dec_helper.
      - destruct (eq_dec_iptr x1 x2).
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

  #[global] Existing Instance VMemInt_iptr.

  #[global] Instance ToDvalue_iptr : ToDvalue iptr :=
    { to_dvalue := DVALUE_IPTR }.

  #[global] Instance ToDvalue_Int `{sz : positive} : ToDvalue (@bit_int sz) :=
    { to_dvalue := @DVALUE_I sz }.

  Definition dvalue_int_unsigned (dv : dvalue) : Z
    := match dv with
       | @DVALUE_I sz x => unsigned x
       | DVALUE_IPTR x => to_unsigned x
       | _ => 0
       end.

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
    | Conv_Oom     (s : string)
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

    Definition eval_int_op {Int} `{VMemInt Int} `{ToDvalue Int} (iop:ibinop) (x y: Int) : EOB dvalue :=
      match iop with
      | Add nuw nsw =>
          if orb (andb nuw (mequ (madd_carry x y mzero) mone))
               (andb nsw (mequ (madd_overflow x y mzero) mone))
          then ret (DVALUE_Poison mdtyp_of_int)
          else to_dvalue <$> madd x y

      | Sub nuw nsw =>
          if orb (andb nuw (mequ (msub_borrow x y mzero) mone))
               (andb nsw (mequ (msub_overflow x y mzero) mone))
          then ret (DVALUE_Poison mdtyp_of_int)
          else to_dvalue <$> (msub x y)

      | Mul nuw nsw => 
          (* I1 mul can't overflow, just based on the 4 possible multiplications. *)
          if (option_pred (fun bw => Pos.eqb bw 1) mbitwidth)
          then to_dvalue <$> (mmul x y)
          else
            res <- mmul x y;;
            
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
          res <- mshl x y;;
          
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
                      nres <- mnegative res;;
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
            else
              if (from_option false (fmap (fun min => min =? msigned x) mmin_signed) && (msigned y =? -1))%Z
              then raise_ub "Signed division overflow."
              else if andb ex (negb ((msigned x) mod (msigned y) =? 0))%Z
                   then ret (DVALUE_Poison mdtyp_of_int)
                   else to_dvalue <$> mdivs x y

      | LShr ex =>
          if option_pred (fun bw => (munsigned y) >=? Zpos bw) mbitwidth && negb (dtyp_eqb mdtyp_of_int DTYPE_IPTR)
          then ret (DVALUE_Poison mdtyp_of_int)
          else if andb ex (negb ((munsigned x)
                                   mod (Z.pow 2 (munsigned y)) =? 0))%Z
               then ret (DVALUE_Poison mdtyp_of_int)
               else ret (to_dvalue (mshru x y))

      | AShr ex =>
          if dtyp_eqb mdtyp_of_int DTYPE_IPTR
          then raise_error "Arithmetic shift for iptr."
          else
            if option_pred (fun bw => (munsigned y) >=? Zpos bw) mbitwidth
            then ret (DVALUE_Poison mdtyp_of_int)
            else if andb ex (negb ((munsigned x)
                                     mod (Z.pow 2 (munsigned y)) =? 0))%Z
                 then ret (DVALUE_Poison mdtyp_of_int)
                 else ret (to_dvalue (mshr x y))

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
            else to_dvalue <$> mmods x y
                           
      | And =>
          ret (to_dvalue (mand x y))

      | Or b =>
          if b then
            (* TODO: disjoint causes poison for non-disjoint `or` inputs
               I've currently implemented the disjointness check by
               seeing whether `or` and `xor` give the same result.  
             *)
            if mequ (mor x y) (mxor x y) then
              ret (to_dvalue (mor x y))
            else ret (DVALUE_Poison mdtyp_of_int) 
          else 
            ret (to_dvalue (mor x y))

      | Xor =>
          ret (to_dvalue (mxor x y))
      end.
    Arguments eval_int_op _ _ _ : simpl nomatch.

    (* Evaluate the given iop on the given arguments according to the bitsize *)
    Definition integer_op (bits:positive) (iop:ibinop) (x y:@bit_int bits) : EOB dvalue :=
      eval_int_op iop x y.
    Arguments integer_op _ _ _ _ : simpl nomatch.

  (* Convert written integer constant to corresponding integer with bitsize bits.
     Takes the integer modulo 2^bits. *)
  Definition coerce_integer_to_int (bits:option positive) (i:Z) : EOB dvalue :=
    match bits with
    | Some sz  => ret (@DVALUE_I sz (repr i))
    | None    =>
        i' <- mrepr i;;
        ret (DVALUE_IPTR i')
    end.
  Arguments coerce_integer_to_int _ _ : simpl nomatch.

  (* Integer iop evaluation, called from eval_iop.
     Here the values must be integers. Helper defined
     in order to prevent eval_iop from being recursive. *)
  Definition eval_iop_integer_h (iop : ibinop) (v1 v2 : dvalue) : EOB dvalue.
    refine
      (match v1, v2 with
       | @DVALUE_I sz1 i1, @DVALUE_I sz2 i2 =>
           _
       | DVALUE_IPTR i1, DVALUE_IPTR i2 =>
           eval_int_op iop i1 i2
       | DVALUE_Poison t, _             =>
           match iop with
           | SDiv _ =>
               x <- match v2 with
                   | @DVALUE_I sz2 i2 =>
                       ret (@Integers.signed sz2 i2)
                   | DVALUE_IPTR i2 =>
                       ret (to_Z i2)
                   | _ => raise_error "ill_typed-iop: sdiv"
                   end;;
               if Z.eq_dec x (-1)
               then raise_ub "Signed division poison overflow"
               else ret (DVALUE_Poison t)
           | _ =>
               ret (DVALUE_Poison t)
           end
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
  Definition eval_iop iop v1 v2 : EOB dvalue :=
    match v1, v2 with
    | (DVALUE_Vector t elts1), (DVALUE_Vector _ elts2) =>
      val <- vec_loop (eval_iop_integer_h iop) (List.combine elts1 elts2) ;;
      ret (DVALUE_Vector t val)
    | _, _ => eval_iop_integer_h iop v1 v2
    end.
  Arguments eval_iop _ _ _ : simpl nomatch.

  Definition eval_int_icmp {Int} `{VMI : VMemInt Int} (samesign:bool) icmp (x y : Int) : EOB dvalue :=
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
    ret ((* Check for sign *)
        if samesign && negb (msamesign x y) then
          @DVALUE_Poison (DTYPE_I 1)
        else if c
             then @DVALUE_I 1 (Integers.one)
             else @DVALUE_I 1 (Integers.zero)).
  Arguments eval_int_icmp _ _ _ _ : simpl nomatch.

  Definition double_op (fop:fbinop) (v1:ll_double) (v2:ll_double) : EOB dvalue :=
    match fop with
    | FAdd => ret (DVALUE_Double (b64_plus FT_Rounding v1 v2))
    | FSub => ret (DVALUE_Double (b64_minus FT_Rounding v1 v2))
    | FMul => ret (DVALUE_Double (b64_mult FT_Rounding v1 v2))
    | FDiv => ret (DVALUE_Double (b64_div FT_Rounding v1 v2))
    | FRem => raise_error "unimplemented double operation"
    end.

  Definition float_op (fop:fbinop) (v1:ll_float) (v2:ll_float) : EOB dvalue :=
    match fop with
    | FAdd => ret (DVALUE_Float (b32_plus FT_Rounding v1 v2))
    | FSub => ret (DVALUE_Float (b32_minus FT_Rounding v1 v2))
    | FMul => ret (DVALUE_Float (b32_mult FT_Rounding v1 v2))
    | FDiv => ret (DVALUE_Float (b32_div FT_Rounding v1 v2))
    | FRem => raise_error "unimplemented float operation"
    end.

  Definition eval_fop (fop:fbinop) (v1:dvalue) (v2:dvalue) : EOB dvalue :=
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
        raise_error ("ill_typed-fop: " ++ (show fop))
    end.

  Definition eval_fneg (v:dvalue) : EOB dvalue :=
    match v with
    | DVALUE_Float f  => ret (DVALUE_Float (Float32.neg f))
    | DVALUE_Double f => ret (DVALUE_Double (Float.neg f))
    | DVALUE_Poison t => ret (DVALUE_Poison t)
    | _ => raise_error ("ill_typed-fneg ")
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

  Definition eval_fcmp (fcmp:fcmp) (v1:dvalue) (v2:dvalue) : EOB dvalue :=
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
  Definition index_into_str_dv (v:dvalue) (idx:LLVMAst.int_ast) : EOB dvalue :=
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
  Definition insert_into_str (str:dvalue) (v:dvalue) (idx:LLVMAst.int_ast) : EOB dvalue :=
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

  Definition index_into_vec_dv (elt_typ : dtyp) (v:dvalue) (idx:dvalue) : EOB dvalue.
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

  Definition insert_into_vec_dv (vec_typ : dtyp) (vec:dvalue) (v:dvalue) (idx:dvalue) : EOB dvalue :=
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

  (* Poison not included because of concretize *)
  Unset Elimination Schemes.
  Inductive dvalue_has_dtyp : dvalue -> dtyp -> Prop :=
  | DVALUE_Addr_typ   : forall a, dvalue_has_dtyp (DVALUE_Addr a) DTYPE_Pointer
  | DVALUE_I_typ      : forall sz x, dvalue_has_dtyp (@DVALUE_I sz x) (DTYPE_I sz)
  | DVALUE_IPTR_typ   : forall x, dvalue_has_dtyp (DVALUE_IPTR x) DTYPE_IPTR
  | DVALUE_Double_typ : forall x, dvalue_has_dtyp (DVALUE_Double x) (DTYPE_FP FP_double)
  | DVALUE_Float_typ  : forall x, dvalue_has_dtyp (DVALUE_Float x) (DTYPE_FP FP_float)
  | DVALUE_None_typ   : dvalue_has_dtyp DVALUE_None DTYPE_Void
  | DVALUE_Poison_typ  : forall τ, NO_VOID τ -> dvalue_has_dtyp (DVALUE_Poison τ) τ

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

  Hint Constructors dvalue_has_dtyp : dvalue.

  Section dvalue_has_dtyp_ind.
    Variable P : dvalue -> dtyp -> Prop.
    Hypothesis IH_Addr           : forall a, P (DVALUE_Addr a) DTYPE_Pointer.
    Hypothesis IH_I              : forall sz x, P (@DVALUE_I sz x) (DTYPE_I sz).
    Hypothesis IH_IPTR           : forall x, P (DVALUE_IPTR x) DTYPE_IPTR.
    Hypothesis IH_Poison         : forall t (NV: NO_VOID t), P (DVALUE_Poison t) t.
    Hypothesis IH_Double         : forall x, P (DVALUE_Double x) (DTYPE_FP FP_double).
    Hypothesis IH_Float          : forall x, P (DVALUE_Float x) (DTYPE_FP FP_float).
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
    Rocqlib.proj_sumbool (NO_VOID_dec t) && dtyp_eqb t dt.

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
        if dtyp_eq_dec dt (DTYPE_FP FP_double) then true else false

    | DVALUE_Float x =>
        if dtyp_eq_dec dt (DTYPE_FP FP_float) then true else false

    | DVALUE_Poison t =>
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
  Proof.
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
  Proof.
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
  (* SAZ: TODO - handle nuw and nsf flags for Trun, nneg for Zext *)
  Definition conversion_okb (conv : LLVMAst.conversion_type) (from_dt to_dt : dtyp)  : bool :=
    match conv with
    | Trunc nuw nsw => lift_conv_okb trunc_base_okb from_dt to_dt
    | Sext => lift_conv_okb ext_base_okb from_dt to_dt
    | Zext nneg => lift_conv_okb ext_base_okb from_dt to_dt
    | _ => false
    end.

  (* Assumes:
     [l] is a list of indices treated as a path into the nested structure.
     The function returns true iff the type at the index is equal to [dt]

  *)
  Fixpoint fetch_extract_path l dt_src : EOB dtyp :=
    match l with
    | [] => raise_error "fetch_extract_path: no path"
    | [idx] =>
        if (Z.ltb idx 0) then raise_error "fetch_extract_path: negative index"
        else
          match dt_src with
          | DTYPE_Array len t =>
              if (N.ltb (Z.to_N idx) len) then ret t
              else raise_error "fetch_extract_path: array out of bounds"
          | DTYPE_Struct fts
          | DTYPE_Packed_struct fts =>
              if Nat.ltb (Z.to_nat idx) (length fts)
              then ret (List.nth (Z.to_nat idx) fts DTYPE_Void)
              else raise_error "fetch_extract_path: struct out of bounds"
          | _ => raise_error "fetch_extract_path: invalid type"
          end
    | idx::idxs =>
        if (Z.ltb idx 0) then raise_error "fetch_extract_path: negative index"
        else
          match dt_src with
          | DTYPE_Array len t =>
              if (N.ltb (Z.to_N idx) len)
              then fetch_extract_path idxs t
              else raise_error "fetch_extract_path: array out of bounds"
          | DTYPE_Struct fts
          | DTYPE_Packed_struct fts =>
              if Nat.ltb (Z.to_nat idx) (length fts)
              then let nth_ft := List.nth (Z.to_nat idx) fts DTYPE_Void in
                   fetch_extract_path idxs nth_ft
              else raise_error "fetch_extract_path: struct out of bounds"
          | _ => raise_error "fetch_extract_path: invalid type"
          end
    end.

  Definition check_extract_path l dt_src dt_tgt :=
    match fetch_extract_path l dt_src with
    | raise_ret t => dtyp_eqb t dt_tgt
    | _ => false
    end.

  Lemma check_fetch_extract_path :
    forall idxs d dtx,
      fetch_extract_path idxs d = raise_ret dtx <-> check_extract_path idxs d dtx = true.
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
    | DTYPE_FP fp
    | DTYPE_Vector _ (DTYPE_FP fp) =>
        true
    | _ => false
    end.

  Ltac solve_no_void_dec :=
    solve
      [ unfold Rocqlib.proj_sumbool;
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

  Hint Resolve forall_repeat_true : DVALUE_HAS_DTYP.
  Hint Constructors dvalue_has_dtyp : DVALUE_HAS_DTYP.
  Hint Rewrite Nnat.Nat2N.id : DVALUE_HAS_DTYP.
  Hint Resolve List.repeat_length : DVALUE_HAS_DTYP.
  Hint Extern 1 (NO_VOID _) => solve_no_void : DVALUE_HAS_DTYP.

  Ltac solve_dvalue_has_dtyp :=
    try normalize_array_vector_dtyp;
    solve [autorewrite with DVALUE_HAS_DTYP; subst; cbn; eauto with DVALUE_HAS_DTYP].
 
  Section EvalIopLemmas.

    Lemma eval_iop_integer_h_dtyp :
      forall dx dy dv sz op,
        dvalue_has_dtyp dx (DTYPE_I sz) ->
        dvalue_has_dtyp dy (DTYPE_I sz) ->
        eval_iop_integer_h op dx dy = ret dv ->
        dvalue_has_dtyp dv (DTYPE_I sz).
    Proof.
      intros dx dy dv sz op TYPx TYPy EVAL.
      inversion TYPx; inversion TYPy; subst; cbn in EVAL.
      2,3,4: cbn in *; repeat break_match_hyp; abs_eq; inv EVAL; eauto.
      break_match_hyp; abs_eq.
      dependent destruction e.
      cbn in *.
      destruct op; cbn in EVAL; repeat break_match_hyp.
      all: abs_eq; inv EVAL; constructor; now cbn.
    Qed.    

    Lemma eval_iop_dtyp_i :
      forall dx dy dv sz op,
        dvalue_has_dtyp dx (DTYPE_I sz) ->
        dvalue_has_dtyp dy (DTYPE_I sz) ->
        eval_iop op dx dy = ret dv ->
        dvalue_has_dtyp dv (DTYPE_I sz).
    Proof.
      intros dx dy dv sz op TYPx TYPy EVAL.
      unfold eval_iop in EVAL.
      inversion TYPx; inversion TYPy; subst; try lia.
      all: eapply eval_iop_integer_h_dtyp in EVAL; eauto.
    Qed.

    Lemma eval_iop_integer_h_dtyp_iptr :
      forall dx dy dv op,
        dvalue_has_dtyp dx DTYPE_IPTR ->
        dvalue_has_dtyp dy DTYPE_IPTR ->
        eval_iop_integer_h op dx dy = ret dv ->
        dvalue_has_dtyp dv DTYPE_IPTR.
    Proof.
      intros dx dy dv op TYPx TYPy EVAL.
      inversion TYPx; inversion TYPy; subst.
      2,3,4: cbn in *; repeat break_match_hyp; abs_eq; inv EVAL; eauto.
      destruct op; cbn in EVAL; repeat break_match_hyp.
      all: abs_eq.
      all: inv EVAL; try (constructor; now cbn).
      Set Printing All.
      all: rewrite VMemInt_iptr_dtyp; constructor; now cbn.
    Qed.
    
    Lemma eval_iop_dtyp_iptr :
      forall dx dy dv op,
        dvalue_has_dtyp dx DTYPE_IPTR ->
        dvalue_has_dtyp dy DTYPE_IPTR ->
        eval_iop op dx dy = ret dv ->
        dvalue_has_dtyp dv DTYPE_IPTR.
    Proof.
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
  Fixpoint default_dvalue_of_dtyp (dt : dtyp) : EOB dvalue :=
    match dt with
    | DTYPE_I sz => ret (default_dvalue_of_dtyp_i sz)
    | DTYPE_IPTR => ret (DVALUE_IPTR zero_iptr)
    | DTYPE_Pointer => ret (DVALUE_Addr null)
    | DTYPE_Void => raise_error "DTYPE_Void is not a true LLVM value"
    | DTYPE_FP FP_float => ret (DVALUE_Float Float32.zero)
    | DTYPE_FP FP_double => ret (DVALUE_Double (Float32.to_double Float32.zero))
    | DTYPE_FP fp => raise_error ("Unimplemented default type: floating point " ++ show fp)
    | DTYPE_Label => raise_error "Unimplemented default type: label"
    | DTYPE_Token => raise_error "Unimplemented default type: token"                             
    | DTYPE_Metadata => raise_error "Unimplemented default type: metadata"
    | DTYPE_X86_mmx => raise_error "Unimplemented default type: x86_mmx"
    | DTYPE_Opaque => raise_error "Unimplemented default type: opaque"
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
    (*     raise_error ("Negative array length for generating default value" ++ *)
    (*     "of DTYPE_Array or DTYPE_Vector") *)
    | DTYPE_Vector sz (DTYPE_FP FP_float) =>
        ret (DVALUE_Vector dt
               (repeat (DVALUE_Float Float32.zero) (N.to_nat sz)))
    | DTYPE_Vector sz (DTYPE_FP FP_double) =>
        ret (DVALUE_Vector dt
               (repeat (DVALUE_Double (Float32.to_double Float32.zero))
                       (N.to_nat sz)))
    (* | DTYPE_Vector sz (DTYPE_X86_fp80) => *)
    (*   if (0 <=? sz) then *)
    (*     (ret (DVALUE_Vector *)
    (*             (repeat (DVALUE_Float Float32.zero) (N.to_nat sz)))) *)
    (*   else *)
    (*     raise_error ("Negative array length for generating default value" ++ *)
    (*     "of DTYPE_Array or DTYPE_Vector") *)
    (* | DTYPE_Vector sz (DTYPE_Fp128) => *)
    (*   if (0 <=? sz) then *)
    (*     (ret (DVALUE_Vector *)
    (*             (repeat (DVALUE_Float Float32.zero) (N.to_nat sz)))) *)
    (*   else *)
    (*     raise_error ("Negative array length for generating default value" ++ *)
    (*     "of DTYPE_Array or DTYPE_Vector") *)
    | DTYPE_Vector sz (DTYPE_I n) =>
        let v := default_dvalue_of_dtyp_i n in
        ret (DVALUE_Vector dt (repeat v (N.to_nat sz)))

    | DTYPE_Vector sz DTYPE_Pointer =>
        ret (DVALUE_Vector dt (repeat (DVALUE_Addr null) (N.to_nat sz)))

    | DTYPE_Vector sz DTYPE_IPTR =>
        ret (DVALUE_Vector dt (repeat (DVALUE_IPTR zero_iptr) (N.to_nat sz)))

    | DTYPE_Vector _ _ => raise_error ("Non-valid or unsupported vector type when generating default vector")
    | DTYPE_Struct fields =>
        v <- map_monad default_dvalue_of_dtyp fields;;
        ret (DVALUE_Struct v)
    | DTYPE_Packed_struct fields =>
        v <- map_monad default_dvalue_of_dtyp fields;;
        ret (DVALUE_Packed_struct v)
    end.
   
  Lemma dvalue_default_NO_VOID :
    forall t v, default_dvalue_of_dtyp t = raise_ret v -> NO_VOID t.
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
      edestruct map_monad_EOB_success; eauto.
    - cbn in *.
      break_match_hyp_inv.
      rewrite FORALL_forall.
      rewrite Forall_forall.
      intros.
      edestruct map_monad_EOB_success; eauto.
    - cbn in H.
      repeat break_match_hyp_inv; cbn; auto.
  Qed.
 
  Lemma dvalue_default : forall t v,
      default_dvalue_of_dtyp t = ret v ->
      dvalue_has_dtyp v t.
  Proof using.
    intros t v. revert v.
    induction t; try do_it;
      try (intros; subst; inversion H; constructor).
    - intros; destruct f; simpl in *; inversion H; econstructor.
    - intros. subst. inversion H. clear H.
      break_match_hyp_inv.
      constructor.
      + eapply dvalue_default_NO_VOID. apply Heqe.
      + apply forall_repeat_true. eapply IHt. reflexivity.
      + rewrite repeat_length. reflexivity.
    - intros.
      cbn in H0.
      repeat break_match_hyp_inv.
      constructor.
      apply map_monad_EOB_Forall2 in Heqe.
      (* could be prettier *)
      induction Heqe; auto.
      constructor.
      eapply H; auto. left; reflexivity.
      eapply IHHeqe; auto.
      intros.
      eapply H. right; auto. assumption.
    - intros.
      cbn in H0.
      repeat break_match_hyp_inv.
      constructor.
      apply map_monad_EOB_Forall2 in Heqe.
      (* could be prettier *)
      induction Heqe; auto.
      constructor.
      eapply H; auto. left; reflexivity.
      eapply IHHeqe; auto.
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
      + unfold vector_dtyp.
        right. right. right. exists FP_float. auto.
      + unfold vector_dtyp.
        right. right. right. exists FP_double. auto.
  Qed.

End DValue.

Arguments DVALUE_I {Pa} sz.
#[global] Hint Constructors dvalue_has_dtyp : dvalue.
#[global] Hint Resolve forall_repeat_true : DVALUE_HAS_DTYP.
#[global] Hint Constructors dvalue_has_dtyp : DVALUE_HAS_DTYP.
#[global] Hint Rewrite Nnat.Nat2N.id : DVALUE_HAS_DTYP.
#[global] Hint Resolve List.repeat_length : DVALUE_HAS_DTYP.
#[global] Hint Extern 1 (NO_VOID _) => solve_no_void : DVALUE_HAS_DTYP.

