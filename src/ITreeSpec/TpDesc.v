
From Coq Require Import
  Arith.Arith
  Lists.List
  Eqdep (* NOTE: we actually only need this on decidable types... *)
.
From EnTree Require Import
     Basics.HeterogeneousRelations
     Ref.FixTree
.

Section TpDesc.


(* A "number" is either a finite natural number or infinity *)
Inductive Num : Type :=
| TCNum : nat -> Num
| TCInf : Num
.

(**
 ** Expression Kinds
 **)

(* The descriptions of the types of expressions that can be used in type
descriptions *)
Inductive ExprKind : Type@{entree_u} :=
| Kind_unit
| Kind_bool
| Kind_nat
| Kind_num
| Kind_bv (w:nat).

Definition exprKindElem AK : Type@{entree_u} :=
  match AK with
  | Kind_unit => unit
  | Kind_bool => bool
  | Kind_nat => nat
  | Kind_num => Num
  | Kind_bv w => VectorDef.t bool w
  end.

Definition defaultEKElem EK : exprKindElem EK :=
  match EK return exprKindElem EK with
  | Kind_unit => tt
  | Kind_bool => false
  | Kind_nat => 0
  | Kind_num => TCNum 0
  | Kind_bv w => VectorDef.const false w
  end.

Class TpExprOps : Type :=
  {
    TpExprUnOp : ExprKind -> ExprKind -> Type@{entree_u};
    TpExprBinOp : ExprKind -> ExprKind -> ExprKind -> Type@{entree_u};
    dec_eq_UnOp : forall {EK1 EK2} (op1 op2 : TpExprUnOp EK1 EK2), {op1=op2} + {~op1=op2};
    dec_eq_BinOp : forall {EK1 EK2 EK3} (op1 op2 : TpExprBinOp EK1 EK2 EK3), 
      {op1=op2} + {~op1=op2};
    evalUnOp : forall {EK1 EK2} (op: TpExprUnOp EK1 EK2),
      exprKindElem EK1 -> exprKindElem EK2;
    evalBinOp : forall {EK1 EK2 EK3} (op: TpExprBinOp EK1 EK2 EK3),
      exprKindElem EK1 -> exprKindElem EK2 -> exprKindElem EK3;
  }.
Context {Ops:TpExprOps}.


(**
 ** Type descriptions themselves
 **)

Inductive KindDesc : Type@{entree_u} :=
| Kind_Expr (EK:ExprKind)
| Kind_Tp
.

(* Expressions that can be used in type descriptions *)
Inductive TpExpr : ExprKind -> Type@{entree_u} :=
| TpExpr_Const {EK} (c:exprKindElem EK) : TpExpr EK
| TpExpr_Var {EK} (ix:nat) : TpExpr EK
| TpExpr_UnOp {EK1 EK2} (op:TpExprUnOp EK1 EK2) (e:TpExpr EK1) : TpExpr EK2
| TpExpr_BinOp {EK1 EK2 EK3} (op:TpExprBinOp EK1 EK2 EK3)
    (e1:TpExpr EK1) (e2:TpExpr EK2) : TpExpr EK3
.

(* The finite number N as a TpExpr *)
Definition TpExprN (n:nat) : TpExpr Kind_num :=
  @TpExpr_Const Kind_num (TCNum n).

(* The number 0 as a TpExpr *)
Definition TpExprZ : TpExpr Kind_num := @TpExpr_Const Kind_num (TCNum 0).

(* Infinity as a TpExpr *)
Definition TpExprInf : TpExpr Kind_num := @TpExpr_Const Kind_num TCInf.

(* Descriptions of types *)
Inductive TpDesc : Type@{entree_u} :=
(* Monadic function types *)
| Tp_M (R : TpDesc)
| Tp_Pi (A : KindDesc) (B : TpDesc)
| Tp_Arr (A : TpDesc) (B : TpDesc)

(* First-order types *)
| Tp_Kind (K : KindDesc)
| Tp_Pair (A : TpDesc) (B : TpDesc)
| Tp_Sum (A : TpDesc) (B : TpDesc)
| Tp_Sigma (K : KindDesc) (B : TpDesc)
| Tp_Seq (e:TpExpr Kind_num) (A : TpDesc)
| Tp_Void

(* Inductive types and type variables *)
| Tp_Ind (A : TpDesc)
| Tp_Var (n : nat)

(* Explicit substitutions; allow one to represent substitutions of expressions
and types with free variables while only defining substitution of value
environments *)
| Tp_TpSubst (A : TpDesc) (B : TpDesc)
| Tp_ExprSubst (A : TpDesc) (EK:ExprKind) (e : TpExpr EK)
.

(* The type description for natural numbers *)
Definition Tp_Nat := Tp_Kind (Kind_Expr Kind_nat).


(**
 ** Deciding equality of type descriptions
 **)

Definition dec_eq_ExprKind (EK1 EK2:ExprKind) : {EK1=EK2} + {~EK1=EK2}.
Proof. repeat decide equality. Defined.

Lemma dec_eq_exprKElem {EK} (elem1 elem2: exprKindElem EK)
  : {elem1=elem2} + {~elem1=elem2}.
Proof.
  revert elem1 elem2; destruct EK; intros; repeat decide equality.
  revert elem1 elem2; induction w; simpl; intros.
Admitted.

Lemma dec_eq_KindDesc (K1 K2:KindDesc) : {K1=K2} + {~K1=K2}.
Proof. repeat decide equality. Qed.

Lemma dec_eq_TpExpr K (e1 e2 : TpExpr K) : {e1=e2} + {~e1=e2}.
Proof.
  revert e2; induction e1; intro e2; destruct e2; try (right; intro H0; discriminate H0).
  - destruct (dec_eq_exprKElem c c0).
    + rewrite e; left; reflexivity.
    + right; intro e; inversion e; apply inj_pairT2 in H0; apply n; assumption.
  - destruct (Nat.eq_dec ix ix0).
    + rewrite e; left; reflexivity.
    + right; intro e; inversion e; apply n; assumption.
  - destruct (dec_eq_ExprKind EK0 EK1).
    + subst EK0. destruct (dec_eq_UnOp op op0); [ destruct (IHe1 e2) | ].
      * subst op; subst e1; left; reflexivity.
      * right; intro e'; inversion e'; apply n.
        apply inj_pairT2 in H1. assumption.
      * right; intro e'; inversion e'; apply n.
        repeat apply inj_pairT2 in H0. assumption.
    + right; intro e; inversion e. apply n; symmetry; assumption.
  - destruct (dec_eq_ExprKind EK0 EK1); [ destruct (dec_eq_ExprKind EK3 EK2) | ].
    + subst EK0; subst EK3.
      destruct (dec_eq_BinOp op op0);
        [ destruct (IHe1_1 e2_1); [ destruct (IHe1_2 e2_2) | ] | ].
      * subst op0; subst e1_1; subst e1_2. left; reflexivity.
      * right; intro e'; inversion e'; apply n. apply inj_pairT2 in H2; assumption.
      * right; intro e'; inversion e'; apply n. apply inj_pairT2 in H1; assumption.
      * right; intro e'; inversion e'; apply n.
        repeat apply inj_pairT2 in H0. assumption.
    + right; intro e'; inversion e'; apply n; symmetry; assumption.
    + right; intro e'; inversion e'; apply n; symmetry; assumption.
Qed.

Definition dec_eq_TpDesc (T U:TpDesc) : { T = U } + {~ T = U}.
Proof.
(*
  repeat decide equality; try apply dec_eq_ExprKind. apply dec_eq_TpExpr.
Qed.
*)
Admitted.

(* NOTE: we use this simpler version of dec_eq_ExprKind in type-level
computations because it computes faster and is easier to write *)
Definition proveEqExprKind (EK1 EK2 : ExprKind) : option (EK1 = EK2) :=
  match EK1, EK2 return option (EK1 = EK2) with
  | Kind_unit, Kind_unit => Some eq_refl
  | Kind_bool, Kind_bool => Some eq_refl
  | Kind_nat, Kind_nat => Some eq_refl
  | Kind_num, Kind_num => Some eq_refl
  | Kind_bv w1, Kind_bv w2 =>
      match Nat.eq_dec w1 w2 with
      | left e =>
          Some (eq_rect w1 (fun y => Kind_bv w1 = Kind_bv y) eq_refl w2 e)
      | right _ => None
      end
  | _, _ => None
  end.

(* NOTE: we use this simpler version of dec_eq_KindDesc in type-level
computations because it computes faster and is easier to write *)
Definition proveEqKindDesc (K1 K2 : KindDesc) : option (K1 = K2) :=
  match K1, K2 return option (K1 = K2) with
  | Kind_Expr EK1, Kind_Expr EK2 =>
      match proveEqExprKind EK1 EK2 with
      | Some e =>
          Some (eq_rect EK1 (fun ek => Kind_Expr EK1 = Kind_Expr ek) eq_refl EK2 e)
      | None => None
      end
  | Kind_Tp, Kind_Tp => Some eq_refl
  | _, _ => None
  end.


(**
 ** Elements of kind descriptions
 **)

(* An element of a kind *)
Definition kindElem K : Type@{entree_u} :=
  match K with
  | Kind_Tp => TpDesc
  | Kind_Expr K' => exprKindElem K'
  end.

Definition defaultKindElem K : kindElem K :=
  match K return kindElem K with
  | Kind_Tp => Tp_Void
  | Kind_Expr EK => defaultEKElem EK
  end.


(**
 ** Substitution and evaluation for type descriptions
 **)

(* An element of an environment is a value, i.e., an element of some kind *)
Definition TpEnvElem : Type@{entree_u} := { K & kindElem K }.

(* An environment is a substitution from variables to values *)
Definition TpEnv := list TpEnvElem.

(* Add a value to a type environment *)
Definition envConsElem {K} (elem:kindElem K) (env:TpEnv) : TpEnv :=
  cons (existT kindElem K elem) env.

(* Eliminate a TpEnvElem at a particular kind, returning the default element of
that kind if the kind of the head does not match *)
Definition elimTpEnvElem K (elem:TpEnvElem) : kindElem K :=
  match proveEqKindDesc (projT1 elem) K with
  | Some e => eq_rect (projT1 elem) kindElem (projT2 elem) K e
  | None => defaultKindElem K
  end.

(* Get the head value of a TpEnv at a particular kind, returning the default
element of that kind if the kind of the head does not match or env is empty *)
Definition headTpEnv K (env:TpEnv) : kindElem K :=
  match env with
  | nil => defaultKindElem K
  | elem :: _ => elimTpEnvElem K elem
  end.


(* Substitute an environment into a variable of a particular kind at lifting
level n, meaning that the environment is a substitution for the variables
starting at n. Return the new value of the variable if it was substituted for
(meaning it has index n + i for some index i in the environment) or the new
variable number if it was not. *)
Fixpoint substVar n env K var {struct var} : kindElem K + nat :=
  match var with
  | 0 => match n with
         | 0 => inl (headTpEnv K env)
         | S _ => inr 0
         end
  | S var' =>
      match n with
      | 0 => substVar 0 (tail env) K var'
      | S n' =>
          match substVar n' env K var' with
          | inl ret =>
              (* NOTE: if we were doing lifting, this is where we would do it *)
              inl ret
          | inr v_ret => inr (S v_ret)
          end
      end
  end.

(* Evaluate a variable to a value, using the default value for free variables *)
Definition evalVar n env K var : kindElem K :=
  match substVar n env K var with
  | inl v => v
  | inr _ => defaultKindElem K
  end.

(* Substitute an environment at lifting level n into type-level expression e *)
Fixpoint substTpExpr n env {K} (e:TpExpr K) : TpExpr K :=
  match e in TpExpr K return TpExpr K with
  | @TpExpr_Const _ c => TpExpr_Const c
  | @TpExpr_Var _ ix =>
      match substVar n env (Kind_Expr _) ix with
      | inl e' => TpExpr_Const e'
      | inr ix' => TpExpr_Var ix'
      end
  | @TpExpr_UnOp _ _ op e' => TpExpr_UnOp op (substTpExpr n env e')
  | @TpExpr_BinOp _ _ _ op e1 e2 =>
      TpExpr_BinOp op (substTpExpr n env e1) (substTpExpr n env e2)
  end.

(* Evaluate a type-level expression to a value *)
Fixpoint evalTpExpr (env:TpEnv) {K} (e:TpExpr K) : exprKindElem K :=
  match e in TpExpr K return exprKindElem K with
  | @TpExpr_Const _ c => c
  | @TpExpr_Var _ ix => evalVar 0 env (Kind_Expr _) ix
  | @TpExpr_UnOp _ _ op e => evalUnOp op (evalTpExpr env e)
  | @TpExpr_BinOp _ _ _ op e1 e2 =>
      evalBinOp op (evalTpExpr env e1) (evalTpExpr env e2)
  end.

(* Substitute an environment at lifting level n into type description T *)
Fixpoint tpSubst n env (T:TpDesc) : TpDesc :=
  match T with
  | Tp_M R => Tp_M (tpSubst n env R)
  | Tp_Pi A B => Tp_Pi A (tpSubst (S n) env B)
  | Tp_Arr A B => Tp_Arr (tpSubst n env A) (tpSubst n env B)
  | Tp_Kind K => Tp_Kind K
  | Tp_Pair A B => Tp_Pair (tpSubst n env A) (tpSubst n env B)
  | Tp_Sum A B => Tp_Sum (tpSubst n env A) (tpSubst n env B)
  | Tp_Sigma A B => Tp_Sigma A (tpSubst (S n) env B)
  | Tp_Seq e A => Tp_Seq (substTpExpr n env e) (tpSubst n env A)
  | Tp_Void => Tp_Void
  | Tp_Ind A => Tp_Ind (tpSubst (S n) env A)
  | Tp_Var var => match substVar n env Kind_Tp var with
                  | inl U => U
                  | inr var' => Tp_Var var'
                  end
  | Tp_TpSubst A B =>
      Tp_TpSubst (tpSubst (S n) env A) (tpSubst n env B)
  | Tp_ExprSubst A EK e =>
      Tp_ExprSubst (tpSubst (S n) env A) EK (substTpExpr n env e)
  end.

(* Substitute a single value into a type description *)
Definition tpSubst1 {K} (elem:kindElem K) T : TpDesc :=
  tpSubst 0 (cons (existT kindElem K elem) nil) T.


(**
 ** Elements of type descriptions
 **)

(* Unfold an inductive type description Tp_Ind A by substituting the current
environment augmented with the mapping from deBruijn index 0 to Tp_Ind A *)
Definition unfoldIndTpDesc env A : TpDesc :=
  tpSubst 0 (@envConsElem Kind_Tp (tpSubst 0 env (Tp_Ind A)) env) A.

(* Inductively defined elements of a type description *)
Inductive indElem : TpDesc -> Type@{entree_u} :=
| Elem_M {R} (f:FunIx (Tp_M R)) : indElem (Tp_M R)
| Elem_Pi {A B} (f:FunIx (Tp_Pi A B)) : indElem (Tp_Pi A B)
| Elem_Arr {A B} (f:FunIx (Tp_Arr A B)) : indElem (Tp_Arr A B)
| Elem_Kind {K} (elem:kindElem K) : indElem (Tp_Kind K)
| Elem_Pair {A B} (elem1: indElem A) (elem2: indElem B)
  : indElem (Tp_Pair A B)
| Elem_SumL {A B} (elem: indElem A) : indElem (Tp_Sum A B)
| Elem_SumR {A B} (elem: indElem B) : indElem (Tp_Sum A B)
| Elem_Sigma {K B} (elem1: kindElem K) (elem2: indElem (tpSubst1 elem1 B))
  : indElem (Tp_Sigma K B)
| Elem_SeqNil {A} : indElem (Tp_Seq TpExprZ A)
| Elem_SeqInf {A} (f:FunIx (Tp_Arr Tp_Nat (Tp_M A))) :
  indElem (Tp_Seq TpExprInf A)
| Elem_SeqCons {A n} (elem1: indElem A)
    (elem2: indElem (Tp_Seq (TpExprN n) A))
  : indElem (Tp_Seq (TpExprN (S n)) A)
| Elem_SeqCast {A e1 e2} (e: evalTpExpr nil e1 = evalTpExpr nil e2)
    (elem: indElem (Tp_Seq e1 A)) : indElem (Tp_Seq e2 A)
(* No case for Tp_Void *)
| Elem_Ind {A} (elem: indElem (unfoldIndTpDesc nil A))
  : indElem (Tp_Ind A)
(* No case for Tp_Var, since that would be a free variable *)
| Elem_TpSubst {A B}
    (elem: indElem (@tpSubst1 Kind_Tp B A))
  : indElem (Tp_TpSubst A B)
| Elem_ExprSubst {A EK e}
    (elem: indElem (@tpSubst1 (Kind_Expr EK) (evalTpExpr nil e) A))
  : indElem (Tp_ExprSubst A EK e)
.

(* Helper function to build a vector indElem with a constant size *)
Fixpoint mkVecIndElemConst {T n} :
  VectorDef.t (indElem T) n -> indElem (Tp_Seq (TpExprN n) T) :=
  match n return VectorDef.t (indElem T) n -> indElem (Tp_Seq (TpExprN n) T) with
  | 0 => fun _ => Elem_SeqNil
  | S n' =>
       fun elems =>
         Elem_SeqCons (VectorDef.hd elems) (mkVecIndElemConst (VectorDef.tl elems))
  end.

(* Helper type for representing an inductive element of a sequence type *)
Definition mseqIndElem (len:Num) A : Type@{entree_u} :=
  match len with
  | TCNum n => VectorDef.t (indElem A) n
  | TCInf => FunIx (Tp_Arr Tp_Nat (Tp_M A))
  end.

(* Helper function to build a sequence indElem from an mseqIndElem *)
Definition mkSeqIndElem {T} {e:TpExpr Kind_num}
  (elems:mseqIndElem (evalTpExpr nil e) T) : indElem (Tp_Seq e T).
Proof.
  apply (Elem_SeqCast (e1:=@TpExpr_Const Kind_num (evalTpExpr nil e)));
    [ reflexivity | ].
  destruct (evalTpExpr nil e).
  - apply mkVecIndElemConst. assumption.
  - apply Elem_SeqInf. apply elems.
Defined.

(** Inversion rules for indElem **)

Definition indElem_invM {R} (elem : indElem (Tp_M R)) : FunIx (Tp_M R).
Proof. inversion elem. assumption. Defined.

Definition indElem_invPi {K B} (elem : indElem (Tp_Pi K B)) : FunIx (Tp_Pi K B).
Proof. inversion elem. assumption. Defined.

Definition indElem_invArr {A B} (elem : indElem (Tp_Arr A B)) : FunIx (Tp_Arr A B).
Proof. inversion elem. assumption. Defined.

Definition indElem_invKind {K} (elem : indElem (Tp_Kind K)) : kindElem K.
Proof. inversion elem. assumption. Defined.

Definition indElem_invPair {A B} (elem : indElem (Tp_Pair A B)) : indElem A * indElem B.
Proof. inversion elem; split; assumption. Defined.

Definition indElem_invSum {A B} (elem : indElem (Tp_Sum A B)) : indElem A + indElem B.
Proof. inversion elem; constructor; assumption. Defined.

Definition indElem_invSigma {K B} (elem : indElem (Tp_Sigma K B)) :
  { elem : kindElem K & indElem (tpSubst1 elem B) }.
Proof. inversion elem; econstructor; eassumption. Defined.

Definition indElem_invSeq {A e} (elem : indElem (Tp_Seq e A)) :
  mseqIndElem (evalTpExpr nil e) A.
Proof.
  - remember (Tp_Seq e A) as T. revert A e HeqT; induction elem; intros; inversion HeqT.
    + apply VectorDef.nil.
    + subst A0. apply f.
    + subst A0. apply VectorDef.cons; [ apply elem1 | ].
      apply (IHelem2 _ _ eq_refl).
    + subst e2. rewrite <- e. apply IHelem. subst A0. reflexivity.
Defined.

Definition indElem_invVoid (elem : indElem Tp_Void) : False.
Proof. inversion elem. Defined.

Definition indElem_invInd {A} (elem : indElem (Tp_Ind A)) :
  indElem (unfoldIndTpDesc nil A).
Proof. inversion elem; assumption. Defined.

Definition indElem_invVar {A} (elem : indElem (Tp_Var A)) : False.
Proof. inversion elem. Defined.

Definition indElem_invTpSubst {A B} (elem : indElem (Tp_TpSubst A B))
  : indElem (@tpSubst1 Kind_Tp B A).
Proof. inversion elem; assumption. Defined.

Definition indElem_invExprSubst {A EK e} (elem : indElem (Tp_ExprSubst A EK e))
  : indElem (@tpSubst1 (Kind_Expr EK) (evalTpExpr nil e) A).
Proof. inversion elem. apply inj_pairT2 in H2. subst e1. assumption. Defined.


(*
(* Elements of a type description relative to an environment *)
Fixpoint tpElemEnv env T : Type@{entree_u} :=
  match T with
  | Tp_M R => FunIx (tpSubst 0 env (Tp_M R))
  | Tp_Pi K B => FunIx (tpSubst 0 env (Tp_Pi K B))
  | Tp_Arr A B => FunIx (tpSubst 0 env (Tp_Arr A B))
  | Tp_Kind K => kindElem K
  | Tp_Pair A B => tpElemEnv env A * tpElemEnv env B
  | Tp_Sum A B => tpElemEnv env A + tpElemEnv env B
  | Tp_Sigma K B => { elem: kindElem K & tpElemEnv (envConsElem elem env) B }
  | Tp_Seq A e =>
      match evalTpExpr env e with
      | TCInf => FunIx (Tp_Arr Tp_Nat (tpSubst 0 env A))
      | TCNum n => VectorDef.t (tpElemEnv env A) n
      end
  | Tp_Void => Empty_set
  | Tp_Ind A => indElem nil (unfoldIndTpDesc env A)
  | Tp_Var var => indElem nil (evalVar 0 env Kind_Tp var)
  | Tp_TpSubst A B =>
      tpElemEnv (@envConsElem Kind_Tp (tpSubst 0 env B) env) A
  | Tp_ExprSubst A EK e =>
      tpElemEnv (@envConsElem (Kind_Expr EK) (evalTpExpr env e) env) A
  end.

(* Elements of a type description = elements relative to the empty environment *)
Definition tpElem := tpElemEnv nil.

(* Convert an inductively-defined element to a recursively-defined one *)
Fixpoint indToTpElem env {T} (elem : indElem env T) : tpElemEnv env T.
  destruct elem.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - split; apply indToTpElem; assumption.
  - left; apply indToTpElem; assumption.
  - right; apply indToTpElem; assumption.
  - exists elem1. apply indToTpElem; assumption.
  - apply VectorDef.nil.
  - simpl. apply f.
  - apply VectorDef.cons;
      [ apply (indToTpElem env _ elem1) | apply (indToTpElem env _ elem2) ].
  - simpl. rewrite <- e. apply (indToTpElem env _ elem).
  - apply elem.
  - apply elem.
  - simpl; apply indToTpElem; assumption.
  - simpl; apply indToTpElem; assumption.
Defined.

(* Convert a recursively-defined element to an inductively-defined one *)
Fixpoint tpToIndElem env {T} : tpElemEnv env T -> indElem env T.
  destruct T; intro elem.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; destruct elem; apply tpToIndElem; assumption.
  - destruct elem; [ apply Elem_SumL | apply Elem_SumR ];
      apply tpToIndElem; assumption.
  - econstructor. apply (tpToIndElem _ _ (projT2 elem)).
  - apply (Elem_SeqCast (e1 := @TpExpr_Const Kind_num (evalTpExpr env e)));
      [ reflexivity | ].
    remember (evalTpExpr env e) as n. simpl in elem. rewrite <- Heqn in elem.
    destruct n.
    + apply mkVecIndElemConst. apply (VectorDef.map (tpToIndElem env T) elem).
    + apply Elem_SeqInf. apply elem.
  - destruct elem.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; apply tpToIndElem; assumption.
  - constructor; apply tpToIndElem; assumption.
Defined.
*)


(**
 ** Function elements of type descriptions
 **)

(* A tuple of inputs to a functional type description *)
Fixpoint TpFunInput env (T:TpDesc) : Type@{entree_u} :=
  match T with
  | Tp_M _ => unit
  | Tp_Pi K B => { elem:kindElem K & TpFunInput (envConsElem elem env) B }
  | Tp_Arr A B => indElem (tpSubst 0 env A) * TpFunInput env B
  | _ => Empty_set
  end.

(* The output type of a monadic function of type T with the given inputs *)
Fixpoint TpFunOutput {env T} : TpFunInput env T -> Type@{entree_u} :=
  match T return TpFunInput env T -> Type with
  | Tp_M R => fun _ => indElem (tpSubst 0 env R)
  | Tp_Pi K B => fun args => TpFunOutput (projT2 args)
  | Tp_Arr A B => fun args => TpFunOutput (snd args)
  | _ => fun _ => unit
  end.

(* The above define input and output function types for TpDescs *)
Global Instance IsTpDesc_TpDesc : IsTpDesc TpDesc :=
  {|
    FunInput := @TpFunInput nil;
    FunOutput := @TpFunOutput nil;
    dec_eq_Tp := dec_eq_TpDesc
  |}.

(* A monadic function of a given type description *)
Fixpoint indFun (E:EvType) env T : Type@{entree_u} :=
  match T with
  | Tp_M R => fixtree TpDesc E (indElem (tpSubst 0 env R))
  | Tp_Pi K B => forall (elem:kindElem K), indFun E (envConsElem elem env) B
  | Tp_Arr A B => indElem (tpSubst 0 env A) -> indFun E env B
  | _ => unit
  end.

(* Convert a monadic function to an FxInterp relative to an environment *)
Fixpoint indFunToInterpEnv {E env T} : indFun E env T ->
                                       forall args:TpFunInput env T,
                                         fixtree TpDesc E (TpFunOutput args) :=
  match T return indFun E env T ->
                 forall args:TpFunInput env T,
                   fixtree TpDesc E (TpFunOutput args) with
  | Tp_M R => fun m _ => m
  | Tp_Pi K B => fun f args => indFunToInterpEnv (f (projT1 args)) (projT2 args)
  | Tp_Arr A B => fun f args => indFunToInterpEnv (f (fst args)) (snd args)
  | _ => fun _ _ => Monad.ret tt
  end.

(* Convert a monadic function to an FxInterp in the top-level environment *)
Definition indFunToInterp {E T} : indFun E nil T -> @FxInterp TpDesc _ E T :=
  indFunToInterpEnv.

(* Convert an FxInterp to a monadic function relative to an environment *)
Fixpoint interpToIndFunEnv {E env T} : (forall args:TpFunInput env T,
                                           fixtree TpDesc E (TpFunOutput args)) ->
                                       indFun E env T :=
  match T return (forall args:TpFunInput env T,
                     fixtree TpDesc E (TpFunOutput args)) ->
                 indFun E env T with
  | Tp_M R => fun f => f tt
  | Tp_Pi K B => fun f elem =>
                   interpToIndFunEnv (fun args => f (existT _ elem args))
  | Tp_Arr A B => fun f arg =>
                    interpToIndFunEnv (fun args => f (arg, args))
  | _ => fun _ => tt
  end.

(* Convert an FxInterp to a monadic function in the top-level environment *)
Definition interpToIndFun {E T} : @FxInterp TpDesc _ E T -> indFun E nil T :=
  interpToIndFunEnv.

End TpDesc.
