From Coq Require Import
     Program
     Setoid
     Morphisms
     Relations
     Logic.FinFun
.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.Utils
     Basics.HeterogeneousRelations
     Eq.Paco2.

From EnTree Require Import
     Basics.HeterogeneousRelations
     Core.EnTreeDefinition
     Core.SubEvent
.

Local Open Scope entree_scope.

Set Printing Universes.

Inductive TpEnc : Type@{entree_u} :=
  | TpEnc_nat : TpEnc
  | TpEnc_unit : TpEnc
  | TpEnc_pair : TpEnc -> TpEnc -> TpEnc
  | TpEnc_sum : TpEnc -> TpEnc -> TpEnc
  | TpEnc_fun : TpEnc -> TpEnc -> TpEnc
  | TpEnc_prop : Prop -> TpEnc
  | TpEnc_list : TpEnc -> TpEnc
  | TpEnc_Vec : nat -> TpEnc -> TpEnc.
Check TpEnc : Type@{Set + 1}.


Variant SpecEvent (E : Type@{entree_u}) : Type@{entree_u}:=
  | Spec_vis (e : E)
  | Spec_forall (tp : TpEnc)
  | Spec_exists (tp : TpEnc).
Arguments Spec_vis {_}.
Arguments Spec_forall {_}.
Arguments Spec_exists {_}.

Fixpoint TpEnc_enc (tp : TpEnc) : Type@{entree_u} :=
  match tp with
  | TpEnc_nat => nat
  | TpEnc_unit => unit
  | TpEnc_pair tp1 tp2 => (TpEnc_enc tp1) * (TpEnc_enc tp2)
  | TpEnc_sum tp1 tp2 => (TpEnc_enc tp1) + (TpEnc_enc tp2)
  | TpEnc_fun tp1 tp2 => (TpEnc_enc tp1) -> (TpEnc_enc tp2)
  | TpEnc_prop P => P
  | TpEnc_list tp => list (TpEnc_enc tp)
  | TpEnc_Vec n tp => False
  end.

#[global] Instance TpEnc_enc_inst : EncodedType TpEnc := TpEnc_enc.

#[global] Instance encoded_SpecEvent E `{EncodedType E} : EncodedType (SpecEvent E) :=
  fun s => 
    match s with
    | Spec_vis e => encodes e
    | Spec_forall tp => encodes tp
    | Spec_exists tp => encodes tp 
end.

Class QIndex (T : Type) :=
  {
    enc : TpEnc;
    index : encodes enc -> T;
    index_surj : Surjective index
  }.

#[global] Instance SpecEventReSum E1 E2 `{ReSum E1 E2} : ReSum E1 (SpecEvent E2) :=
  fun e => Spec_vis (resum e).
#[global] Instance SpecEventReSumRet E1 E2 {EncE1 : EncodedType E1} {EncE2 : EncodedType E2} {Res : ReSum E1 E2}
 {ResRet : ReSumRet E1 E2} : ReSumRet E1 (SpecEvent E2) := fun e x => @resum_ret _ _ _ _ _ ResRet e x.

Definition entree_spec E `{EncodedType E} R := entree (SpecEvent E) R.
Notation entree_spec' E R := (entree' (SpecEvent E) R).

Create HintDb entree_spec.

Section refines.

Context {E1 E2 : Type} `{EncodedType E1} `{EncodedType E2} {R1 R2 : Type}.

Context (RPre : E1 -> E2 -> Prop) (RPost : forall (e1 : E1) (e2 : E2), encodes e1 -> encodes e2 -> Prop) (RR : R1 -> R2 -> Prop).

Inductive refinesF (sim : entree_spec E1 R1 -> entree_spec E2 R2 -> Prop) : entree_spec' E1 R1 -> entree_spec' E2 R2 -> Prop := 
  | refinesF_Ret r1 r2 : RR r1 r2 -> refinesF sim (RetF r1) (RetF r2)
  | refinesF_Tau t1 t2 : sim t1 t2 -> refinesF sim (TauF t1) (TauF t2)
  | refinesF_Vis e1 e2 k1 k2 : RPre e1 e2 -> (forall a b, RPost e1 e2 a b -> sim (k1 a) (k2 b) ) ->
                               refinesF sim (VisF (Spec_vis e1) k1) (VisF (Spec_vis e2) k2)
  | refinesF_TauL t1 ot2 : refinesF sim (observe t1) ot2 -> refinesF sim (TauF t1) ot2
  | refinesF_TauR ot1 t2 : refinesF sim ot1 (observe t2) -> refinesF sim ot1 (TauF t2)

  | refinesF_forallR A ot1 k : (forall a, refinesF sim ot1 (observe (k a)) ) -> refinesF sim ot1 (VisF (Spec_forall A) k)
  | refinesF_existsR A ot1 k a : refinesF sim ot1 (observe (k a)) -> refinesF sim ot1 (VisF (Spec_exists A) k)
  | refinesF_forallL A ot2 k a : refinesF sim (observe (k a)) ot2 -> refinesF sim (VisF (Spec_forall A) k ) ot2
  | refinesF_existsL A ot2 k : (forall a, refinesF sim (observe (k a)) ot2) -> refinesF sim (VisF (Spec_exists A) k) ot2
.

Hint Constructors refinesF : entree_spec.

Definition refines_ sim : entree_spec E1 R1 -> entree_spec E2 R2 -> Prop :=
  fun t1 t2 => refinesF sim (observe t1) (observe t2).

Lemma monotone_refinesF ot1 ot2 sim sim' (LE : sim <2= sim')
      (IN : refinesF sim ot1 ot2) : refinesF sim' ot1 ot2.
Proof with eauto with entree_spec.
  induction IN...
Qed.

Lemma monotone_refines_: monotone2 refines_.
Proof. red. intros. eapply monotone_refinesF; eauto. Qed.

Hint Resolve monotone_refines_ : paco.

Definition refines := paco2 refines_ bot2.

End refines.

(* what is *)
Definition forall_spec {E} `{EncodedType E} (A : Type) `{QIndex A} : entree_spec E A :=
  Vis (Spec_forall enc) (fun x : encodes (Spec_forall enc) => Ret (index x)).

Lemma forall_spec_correctr {E1 E2} `{EncodedType E1} `{EncodedType E2} 
      (A : Type) `{QIndex A} R1 R2  RPre RPost RR
      (k : A -> entree_spec E2 R1) (t : entree_spec E1 R2) :
  (forall a : A, refines RPre RPost RR t (k a)) ->
  refines RPre RPost RR t (EnTree.bind (forall_spec A) k).
Proof.
  intros. pstep. red. cbn. constructor. cbn. intros. simpl.
  pstep_reverse. auto with entree_spec. apply monotone_refines_.
  apply H2.
Qed.

Lemma forall_spec_correctl {E1 E2} `{EncodedType E1} `{EncodedType E2} 
      (A : Type) `{QIndex A} R1 R2  RPre RPost RR
      (k : A -> entree_spec E2 R1) (t : entree_spec E1 R2) :
  (exists a : A, refines RPre RPost RR (k a) t) ->
  refines RPre RPost RR (EnTree.bind (forall_spec A) k) t.
Proof.
  intros. destruct H2 as [a Ha]. pstep. red.
  specialize (index_surj a) as [x Hx]. econstructor.
  Unshelve. 2 : exact x. rewrite Hx. simpl. pstep_reverse.
  apply monotone_refines_.
Qed.

Definition exists_spec {E} `{EncodedType E} (A : Type) `{QIndex A} : entree_spec E A :=
  Vis (Spec_exists enc) (fun x : encodes (Spec_exists enc) => Ret (index x)).

Lemma exists_spec_correctr {E1 E2} `{EncodedType E1} `{EncodedType E2} 
      (A : Type) `{QIndex A} R1 R2  RPre RPost RR
      (k : A -> entree_spec E2 R1) (t : entree_spec E1 R2) :
  (exists a : A, refines RPre RPost RR t (k a)) ->
  refines RPre RPost RR t (EnTree.bind (exists_spec A) k).
Proof.
  intros. destruct H2 as [a Ha]. pstep. red.
  specialize (index_surj a) as [x Hx]. econstructor.
  Unshelve. 2 : exact x. rewrite Hx. simpl. pstep_reverse.
  apply monotone_refines_.
Qed.

Lemma exists_spec_correctl {E1 E2} `{EncodedType E1} `{EncodedType E2} 
      (A : Type) `{QIndex A} R1 R2  RPre RPost RR
      (k : A -> entree_spec E2 R1) (t : entree_spec E1 R2) :
  (forall a : A, refines RPre RPost RR t (k a)) ->
  refines RPre RPost RR t (EnTree.bind (forall_spec A) k).
Proof.
  intros. pstep. red. cbn. constructor. cbn. intros. simpl.
  pstep_reverse. auto with entree_spec. apply monotone_refines_.
  apply H2.
Qed.

(*
Definition assume_spec {E} `{EncodedType E} (P : Prop) : entree_spec E unit :=
  Vis (Spec_forall P) (fun _ => Ret tt).
Definition assert_spec {E} `{EncodedType E} (P : Prop) : entree_spec E unit :=
  Vis (Spec_exists P) (fun _ => Ret tt).
Definition forall_spec {E} `{EncodedType E} (A : Set) : entree_spec E A :=
  Vis (Spec_forall A) (fun a => Ret a).
Definition exists_spec {E} `{EncodedType E} (A : Set) : entree_spec E A :=
  Vis (Spec_exists A) (fun a => Ret a).
*)
