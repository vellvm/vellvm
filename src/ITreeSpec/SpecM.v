From ITree Require Import
     Basics.HeterogeneousRelations
     Core.ITreeDefinition.

From ITreeSpec Require Import
  ITreeSpecDefinition
  FixTree
  TpDesc.

From Stdlib Require Import
  Arith.Arith
  Strings.String
  Lists.List.

Import Monads.

Fixpoint vec_mapM@{u} {A B:Type@{u}} {M} `{Monad@{u u} M} (f : A -> M B) n (v : VectorDef.t A n)
  : M (VectorDef.t B n) :=
  match v with
  | VectorDef.nil _ => Monad.ret (VectorDef.nil B)
  | VectorDef.cons _ a n' v' =>
      Monad.bind (f a)
        (fun b =>
           Monad.bind (vec_mapM f n' v')
             (fun vb => Monad.ret (VectorDef.cons B b n' vb)))
  end.


(**
 ** EncodingType and ReSum instances for defining SpecM
 **)

(* The error event type *)
Inductive ErrorE : Set :=
| mkErrorE : string -> ErrorE.

Global Instance EncodingType_ErrorE : EncodingType ErrorE := fun _ => Empty_set.

(* The event type for SpecM computations, given an underlying event type *)
Definition SpecE (E : EvType) : Type@{entree_u} :=
  SpecEvent (ErrorE + E).

(* The return type for a SpecEE effect in a SpecM computation *)
Definition SpecERet E (e:SpecE E) : Type@{entree_u} := encodes e.

Definition SpecEv E : EvType := Build_EvType (SpecE E) _.

Global Instance EncodingType_SpecE E : EncodingType (SpecE E) := SpecERet E.

Global Instance ReSum_SpecE_E (E : EvType) : ReSum E (SpecE E) :=
  fun e => Spec_vis (inr e).

Global Instance ReSumRet_SpecE_E (E : EvType) : ReSumRet E (SpecE E) :=
  fun _ r => r.

Global Instance ReSum_SpecE_Error (E : EvType) : ReSum ErrorE (SpecE E) :=
  fun e => Spec_vis (inl e).

Global Instance ReSumRet_SpecE_Error (E : EvType) : ReSumRet ErrorE (SpecE E) :=
  fun _ r => r.


(**
 ** The SpecM monad
 **)

Section SpecM.
Context {Ops:TpExprOps}.


(* The SpecM monad is an entree spec over SpecE events *)
Definition SpecM (E:EvType) A : Type := fixtree TpDesc (SpecEv E) A.

#[global] Instance Monad_SpecM E : Monad (SpecM E) := Monad_fixtree _ _.

(* The monadic operations on SpecM *)
Definition RetS {E A} (a : A) : SpecM E A := ret a.
Definition BindS {E A B} (m : SpecM E A) (k : A -> SpecM E B) := bind m k.

(* Specification combinators as monadic operations *)
Definition ForallS {E} (A : Type) `{QuantType A} : SpecM E A :=
  Fx_Vis (Spec_forall quantEnc : SpecEv E) (fun x => Fx_Ret (quantEnum x)).
Definition ExistsS {E} (A : Type) `{QuantType A} : SpecM E A :=
  Fx_Vis (Spec_exists quantEnc : SpecEv E) (fun x => Fx_Ret (quantEnum x)).

(* Assumptions and assertions as monadic operations *)
Definition AssumeS {E} (P : Prop) : SpecM E unit :=
  BindS (ForallS P) (fun _ => ret tt).
Definition AssertS {E} (P : Prop) : SpecM E unit :=
  BindS (ExistsS P) (fun _ => ret tt).

(* Trigger a domain-specific event in the E type *)
Definition TriggerS {E:EvType} (e : E) : SpecM E (encodes e) :=
  Fx_Vis (resum e : SpecEv E) (fun x => Fx_Ret x).

(* Signal an error *)
Definition ErrorS {E A} (str : string) : SpecM E A :=
  Fx_Vis ((Spec_vis (inl (mkErrorE str))) : SpecEv E)
    (fun (x:Empty_set) => match x with end).

(* An error computation in the underlying entree type, to define interp_SpecM *)
Definition errorEntree {E R} (s : string) : entree (SpecEv E) R :=
  Vis (Spec_vis (inl (mkErrorE s))) (fun v:Empty_set => match v with end).

(* Interpret a SpecM computation as an entree *)
Definition interp_SpecM {E R} (t:SpecM E R) : entree (SpecEv E) R :=
  interp_fixtree (@errorEntree E R "Unbound function call") nil t.


(**
 ** Specification Elements of Type Descriptions
 **)

(* An infinite stream represented as a function from a natural number index to
the element at that index *)
Inductive Stream (A:Type@{entree_u}) : Type@{entree_u} :=
| MkStream (f : nat -> A).

Arguments MkStream {_} _.

(* Get the element of a stream at a particular index *)
Definition streamGet {A} (s:Stream A) i : A :=
  match s with
  | MkStream f => f i
  end.

(* A finite or infinite sequence, where the latter is represented as a monadic
function from the natural number index to the element at that index *)
Definition mseq (E:EvType) len (A:Type@{entree_u}) : Type@{entree_u} :=
  match len with
  | TCNum n => VectorDef.t A n
  | TCInf => Stream (SpecM E A)
  end.

(* Specialized inductive type to indicate if a type description is to be treated
as a monadic function or as a data type *)
Inductive FunFlag : Set := IsFun | IsData.

(* Elements of type descriptions that use monadic functions instead of FunIxs.
If the FunFlag flag is true, we are translating a monadic function type, and
should use funElem *)
Fixpoint tpElemEnv (E:EvType) env (isf : FunFlag) T : Type@{entree_u} :=
  match T with
  | Tp_M R => SpecM E (tpElemEnv E env IsData R)
  | Tp_Pi K B =>
      forall (elem:kindElem K), tpElemEnv E (envConsElem elem env) IsFun B
  | Tp_Arr A B =>
      tpElemEnv E env IsData A -> tpElemEnv E env IsFun B
  | Tp_Kind K =>
      if isf then unit else kindElem K
  | Tp_Pair A B =>
      if isf then unit else tpElemEnv E env IsData A * tpElemEnv E env IsData B
  | Tp_Sum A B =>
      if isf then unit else tpElemEnv E env IsData A + tpElemEnv E env IsData B
  | Tp_Sigma K B =>
      if isf then unit else
        { elem: kindElem K & tpElemEnv E (envConsElem elem env) IsData B }
  | Tp_Seq e A =>
      if isf then unit else mseq E (evalTpExpr env e) (tpElemEnv E env IsData A)
  | Tp_Void => if isf then unit else Empty_set
  | Tp_Ind A =>
      if isf then unit else indElem (unfoldIndTpDesc env A)
  | Tp_Var var =>
      if isf then unit else indElem (tpSubst 0 env (Tp_Var var))
  | Tp_TpSubst A B =>
      if isf then unit else
        tpElemEnv E (envConsElem (K:=Kind_Tp) (tpSubst 0 env B) env) IsData A
  | Tp_ExprSubst A EK e =>
      if isf then unit else
        tpElemEnv E (envConsElem (K:=Kind_Expr EK) (evalTpExpr env e) env) IsData A
  end.

Definition tpElem E T := tpElemEnv E nil IsData T.

Definition specFunEnv E env T := tpElemEnv E env IsFun T.
Definition specFun E T := tpElemEnv E nil IsFun T.

Definition specIndFun E env T := indFun (SpecEv E) env T.


(* Call a function index in a specification *)
Definition callIx {E T} (f : FunIx T) (args : TpFunInput nil T)
  : SpecM E (TpFunOutput args) :=
  Fx_Call (MkFunCall T f args) (fun x => Fx_Ret x).

Axiom callIxSubst : forall {E env} T (f : FunIx (tpSubst 0 env T)) (args : TpFunInput env T),
    SpecM E (TpFunOutput args).

(* Create a function index from a specification function in a specification *)
Definition lambdaIx {E T}
  (f : forall args : TpFunInput nil T, SpecM E (TpFunOutput args)) : SpecM E (FunIx T) :=
  Fx_MkFuns (fun _ => mkMultiFxInterp1 T f) (fun ixs => Fx_Ret (headFunIx ixs)).

Axiom lambdaIxSubst :
  forall {E env} T
         (f : forall args : TpFunInput env T, SpecM E (TpFunOutput args)),
    SpecM E (FunIx (tpSubst 0 env T)).

Axiom subst_nil_eq : forall n T, tpSubst n nil T = T.

Axiom subst1_of_subst_eq :
  forall K (elem : kindElem K) env T,
    tpSubst1 elem (tpSubst 1 env T) = tpSubst 0 (envConsElem elem env) T.

Axiom indElem_invSeqSubst :
  forall {env A e} (elem : indElem (Tp_Seq (substTpExpr 0 env e) A)),
    mseqIndElem (evalTpExpr env e) A.

Axiom unfoldInd_subst_eq :
  forall env A, unfoldIndTpDesc nil (tpSubst 1 env A) = unfoldIndTpDesc env A.

Axiom subst1_eval_nil_subst_eq :
  forall env EK (e : TpExpr EK) A,
    tpSubst1 (K:=Kind_Expr EK)
      (evalTpExpr nil (substTpExpr 0 env e)) (tpSubst 1 env A)
    = tpSubst 0 (envConsElem (K:=Kind_Expr EK) (evalTpExpr env e) env) A.

Axiom mkSeqIndElemSubst :
  forall {env} T (e : TpExpr Kind_num),
    mseqIndElem (evalTpExpr env e) (tpSubst 0 env T) ->
    indElem (tpSubst 0 env (Tp_Seq e T)).


Fixpoint interpToSpecFun E env T {struct T} :
  (forall args:TpFunInput env T, SpecM E (TpFunOutput args)) ->
  specFunEnv E env T :=
  match T return (forall args:TpFunInput env T, SpecM E (TpFunOutput args)) ->
                 specFunEnv E env T with
  | Tp_M R => fun f => Functor.fmap (indToTpElem E env R) (f tt)
  | Tp_Pi K B =>
      fun f elem =>
        interpToSpecFun
          E (envConsElem elem env) B
          (fun args => f (existT _ elem args))
  | Tp_Arr A B =>
      fun f arg =>
        interpToSpecFun E env B
          (fun args =>
             Monad.bind
               (u:= TpFunOutput (T:=B) args)
               (tpToIndElem E env A arg)
               (fun iarg => f (iarg, args)))
  | Tp_Kind K => fun _ => tt
  | Tp_Pair A B => fun _ => tt
  | Tp_Sum A B => fun _ => tt
  | Tp_Sigma K B => fun _ => tt
  | Tp_Seq e A => fun _ => tt
  | Tp_Void => fun _ => tt
  | Tp_Ind A => fun _ => tt
  | Tp_Var var => fun _ => tt
  | Tp_TpSubst A B => fun _ => tt
  | Tp_ExprSubst A EK e => fun _ => tt
  end
with
specFunToInterp E env T {struct T}
  : specFunEnv E env T ->
    (forall args:TpFunInput env T, SpecM E (TpFunOutput args)) :=
  match T return specFunEnv E env T ->
                 (forall args:TpFunInput env T, SpecM E (TpFunOutput args)) with
  | Tp_M R => fun m _ =>
                Monad.bind m (fun r => tpToIndElem E env R r)
  | Tp_Pi K B =>
      fun f args =>
        specFunToInterp E (envConsElem (projT1 args) env) B (f (projT1 args)) (projT2 args)
  | Tp_Arr A B =>
      fun f args =>
        specFunToInterp E env B (f (indToTpElem E env A (fst args))) (snd args)
  | Tp_Kind K => fun _ _ => Monad.ret tt
  | Tp_Pair A B => fun _ _ => Monad.ret tt
  | Tp_Sum A B => fun _ _ => Monad.ret tt
  | Tp_Sigma K B => fun _ _ => Monad.ret tt
  | Tp_Seq e A => fun _ _ => Monad.ret tt
  | Tp_Void => fun _ _ => Monad.ret tt
  | Tp_Ind A => fun _ _ => Monad.ret tt
  | Tp_Var var => fun _ _ => Monad.ret tt
  | Tp_TpSubst A B => fun _ _ => Monad.ret tt
  | Tp_ExprSubst A EK e => fun _ _ => Monad.ret tt
  end
with
indToTpElem E env T {struct T} : indElem (tpSubst 0 env T) -> tpElemEnv E env IsData T :=
  match T return indElem (tpSubst 0 env T) -> tpElemEnv E env IsData T with
  | Tp_M R =>
      fun elem =>
        Functor.fmap (indToTpElem E env R) (callIxSubst (Tp_M R) (indElem_invM elem) tt)
  | Tp_Pi K B =>
      fun elem arg =>
        interpToSpecFun
          E (envConsElem arg env) B
          (fun args =>
             callIxSubst (Tp_Pi K B) (indElem_invPi elem) (existT _ arg args))
  | Tp_Arr A B =>
      fun elem arg =>
        interpToSpecFun E env B
          (fun args =>
             Monad.bind
               (u:=TpFunOutput (T:=B) args)
               (tpToIndElem E env A arg)
               (fun iarg =>
                  callIxSubst (Tp_Arr A B) (indElem_invArr elem) (iarg, args)))
  | Tp_Kind K => fun elem => indElem_invKind elem
  | Tp_Pair A B =>
      fun elem => (indToTpElem E env A (fst (indElem_invPair elem)),
                    indToTpElem E env B (snd (indElem_invPair elem)))
  | Tp_Sum A B =>
      fun elem =>
        match indElem_invSum elem with
        | inl x => inl (indToTpElem E env A x)
        | inr y => inr (indToTpElem E env B y)
        end
  | Tp_Sigma K B =>
      fun elem =>
        existT _ (projT1 (indElem_invSigma elem))
          (indToTpElem E (envConsElem (projT1 (indElem_invSigma elem)) env) B
             (eq_rect _ indElem (projT2 (indElem_invSigma elem)) _
                (subst1_of_subst_eq _ _ _ _)))
  | Tp_Seq e A =>
      fun elem =>
        (match evalTpExpr env e as len return
               mseqIndElem len (tpSubst 0 env A) ->
               mseq E len (tpElemEnv E env IsData A) with
         | TCNum n => fun vec => VectorDef.map (indToTpElem E env A) vec
         | TCInf =>
             fun funix =>
               MkStream
                 (fun n =>
                    Functor.fmap (indToTpElem E env A)
                      (callIxSubst (Tp_Arr Tp_Nat (Tp_M A)) funix
                         (Elem_Kind (K:=Kind_Expr Kind_nat) n, tt)))
         end)
          (indElem_invSeqSubst elem)
  | Tp_Void => fun elem => match indElem_invVoid elem with end
  | Tp_Ind A =>
      fun elem => eq_rect _ indElem (indElem_invInd elem) _
                    (unfoldInd_subst_eq _ _)
  | Tp_Var var => fun elem => elem
  | Tp_TpSubst A B =>
      fun elem =>
        indToTpElem E (@envConsElem _ Kind_Tp (tpSubst 0 env B) env) A
          (eq_rect _ indElem (indElem_invTpSubst elem) _
             (subst1_of_subst_eq _ _ _ _))
  | Tp_ExprSubst A EK e =>
      fun elem =>
        indToTpElem E (@envConsElem _ (Kind_Expr EK) (evalTpExpr env e) env) A
          (eq_rect _ indElem (indElem_invExprSubst elem) _
             (subst1_eval_nil_subst_eq _ _ _ _))
  end
with
tpToIndElem E env T {struct T} : tpElemEnv E env IsData T -> SpecM E (indElem (tpSubst 0 env T)) :=
  match T return tpElemEnv E env IsData T -> SpecM E (indElem (tpSubst 0 env T)) with
  | Tp_M R =>
      fun m =>
        Functor.fmap Elem_M
          (lambdaIxSubst (Tp_M R)
             (fun _ => Monad.bind m (fun r => tpToIndElem E env R r)))
  | Tp_Pi K B =>
      fun f =>
        Functor.fmap Elem_Pi
          (lambdaIxSubst (Tp_Pi K B)
             (fun args =>
                specFunToInterp E (envConsElem (projT1 args) env) B
                  (f (projT1 args)) (projT2 args)))
  | Tp_Arr A B =>
      fun f =>
        Functor.fmap Elem_Arr
          (lambdaIxSubst (Tp_Arr A B)
             (fun args =>
                specFunToInterp E env B
                  (f (indToTpElem E env A (fst args))) (snd args)))
  | Tp_Kind K => fun elem => Monad.ret (Elem_Kind elem)
  | Tp_Pair A B =>
      fun elem =>
        Monad.bind (tpToIndElem E env A (fst elem))
          (fun ielemA =>
             Monad.bind (tpToIndElem E env B (snd elem))
               (fun ielemB => Monad.ret (Elem_Pair ielemA ielemB)))
  | Tp_Sum A B =>
      fun elem =>
        match elem with
        | inl x => Functor.fmap Elem_SumL (tpToIndElem E env A x)
        | inr y => Functor.fmap Elem_SumR (tpToIndElem E env B y)
        end
  | Tp_Sigma K B =>
      fun elem =>
        Functor.fmap
          (fun ielem =>
             Elem_Sigma (projT1 elem)
               (eq_rect _ indElem ielem _ (eq_sym (subst1_of_subst_eq _ _ _ _))))
          (tpToIndElem E (envConsElem (projT1 elem) env) B (projT2 elem))
  | Tp_Seq e A =>
      fun elem =>
        Functor.fmap
          (mkSeqIndElemSubst A e)
          ((match evalTpExpr env e as len return
                  mseq E len (tpElemEnv E env IsData A) ->
                  SpecM E (mseqIndElem len (tpSubst 0 env A)) with
            | TCNum n =>
                fun v => vec_mapM (tpToIndElem E env A) n v
            | TCInf =>
                fun s =>
                  lambdaIxSubst (Tp_Arr Tp_Nat (Tp_M A))
                    (fun args =>
                       Monad.bind (streamGet s (indElem_invKind (fst args))) (tpToIndElem E env A))
            end)
             elem)
  | Tp_Void => fun elem => match elem with end
  | Tp_Ind A =>
      fun elem =>
        Monad.ret (Elem_Ind
                     (eq_rect _ indElem elem _
                        (eq_sym (unfoldInd_subst_eq _ _))))
  | Tp_Var var => fun elem => Monad.ret elem
  | Tp_TpSubst A B =>
      fun elem =>
        Functor.fmap
          (fun ielem =>
             Elem_TpSubst
               (eq_rect _ indElem ielem _
                  (eq_sym (subst1_of_subst_eq _ _ _ _))))
          (tpToIndElem E (@envConsElem _ Kind_Tp (tpSubst 0 env B) env) A elem)
  | Tp_ExprSubst A EK e =>
      fun elem =>
        Functor.fmap
          (fun ielem =>
             Elem_ExprSubst
               (eq_rect _ indElem ielem _
                  (eq_sym (subst1_eval_nil_subst_eq _ _ _ _))))
          (tpToIndElem E (@envConsElem _ (Kind_Expr EK) (evalTpExpr env e) env) A elem)
  end
.


(* Fold an element of an inductive type; note that this must be monadic, because
the inductive type element could contain specFuns, which need to get turned into
function indices *)
Definition foldTpElem {E T} (elem : tpElem E (unfoldIndTpDesc nil T)) :
  SpecM E (tpElem E (Tp_Ind T)) :=
  eq_rect _ (fun U => SpecM E (indElem U)) (tpToIndElem E nil _ elem)
    _ (subst_nil_eq _ _).

(* Unfold an element of an inductive type *)
Definition unfoldTpElem {E T} (elem : tpElem E (Tp_Ind T)) :
  tpElem E (unfoldIndTpDesc nil T) :=
  indToTpElem E nil _ (eq_rect _ indElem elem
                         _ (sym_eq (subst_nil_eq _ _))).


(* Generate a function index for a fixpoint over a single function *)
Definition fixIx {E T} (f: forall (_:FunIx T) (args:TpFunInput nil T),
      SpecM E (TpFunOutput args)) : SpecM E (FunIx T) :=
  Fx_MkFuns
    (fun ixs => mkMultiFxInterp1 T (f (headFunIx ixs)))
    (fun ixs => Fx_Ret (headFunIx ixs)).

(* Monadic join, turning M (M A) into just M A *)
Definition joinM {E A} (m : SpecM E (SpecM E A)) : SpecM E A :=
  Monad.bind m (fun x => x).

(* Do a form of monadic join, turning a computation of a monadic computation
into just a monadic computation *)
Fixpoint joinSpecFun {E env T} : SpecM E (specFunEnv E env T) -> specFunEnv E env T :=
  match T return SpecM E (specFunEnv E env T) -> specFunEnv E env T with
  | Tp_M R => fun m => joinM m
  | Tp_Pi K B =>
      fun mf elem => joinSpecFun (Functor.fmap (fun f => f elem) mf)
  | Tp_Arr A B => fun mf arg => joinSpecFun (Functor.fmap (fun f => f arg) mf)
  | _ => fun _ => tt
  end.

(* Create a lambda as a fixed-point that can call itself. Note that the type of
   f, specFun E T -> specFun E T, is the same as specFun E (Tp_Arr T T) when T
   is a monadic function type. *)
Definition FixS {E T} (f: specFun E T -> specFun E T) : specFun E T :=
  joinSpecFun
    (Functor.fmap
       (fun funix => interpToSpecFun E nil T (callIx funix))
       (fixIx (fun funix =>
                 specFunToInterp E nil T
                   (f (interpToSpecFun E nil T (callIx funix)))))).


(**
 ** Defining a multi-way fixed point
 **)

(* A tuple of spec functions of the given types *)
Fixpoint specFuns E Ts : Type@{entree_u} :=
  match Ts with
  | nil => unit
  | T :: Ts' => specFun E T * specFuns E Ts'
  end.

(* Convert a sequence of function indices to a tuple of specFuns *)
Fixpoint funIxsToSpecFuns {E Ts} : FunIxs Ts -> specFuns E Ts :=
  match Ts return FunIxs Ts -> specFuns E Ts with
  | nil => fun _ => tt
  | T :: Ts' => fun ixs => (interpToSpecFun E nil T (callIx (headFunIx ixs)),
                             funIxsToSpecFuns (tailFunIxs ixs))
  end.

(* Do a joinSpecFun on a tuple of specFuns *)
Fixpoint joinSpecFuns {E Ts} : SpecM E (specFuns E Ts) -> specFuns E Ts :=
  match Ts return SpecM E (specFuns E Ts) -> specFuns E Ts with
  | nil => fun _ => tt
  | T :: Ts' => fun m => (joinSpecFun (Functor.fmap fst m),
                           joinSpecFuns (Functor.fmap snd m))
  end.


(* Build the multi-arity function type specFun E T1 -> ... specFun E Tn -> A *)
Fixpoint arrowSpecFuns E (Ts : list TpDesc) (A : Type@{entree_u}) : Type@{entree_u} :=
  match Ts with
  | nil => A
  | T :: Ts' => specFun E T -> arrowSpecFuns E Ts' A
  end.

(* Apply a multi-arity function over specFuns to a tuple of specFuns *)
Fixpoint applyArrowSpecFuns {E Ts A} : arrowSpecFuns E Ts A -> specFuns E Ts -> A :=
  match Ts return arrowSpecFuns E Ts A -> specFuns E Ts -> A with
  | nil => fun f _ => f
  | T :: Ts' => fun f tup => applyArrowSpecFuns (f (fst tup)) (snd tup)
  end.

(* FIXME: move this somewhere more relevant *)
Arguments MultiFxInterp {_ _} _ _.

(* Convert a specFuns tuple to a MultiFxInterp *)
Fixpoint specFunsToMultiInterp {E Ts} : specFuns E Ts -> MultiFxInterp (SpecEv E) Ts :=
  match Ts return specFuns E Ts -> MultiFxInterp (SpecEv E) Ts with
  | nil => fun _ => mkMultiFxInterp0
  | T :: Ts' =>
      fun fs =>
        consMultiFxInterp (specFunToInterp E nil T (fst fs))
          (specFunsToMultiInterp (snd fs))
  end.

Definition MultiFixBodies E Ts : Type@{entree_u} :=
  arrowSpecFuns E Ts (specFuns E Ts).

Definition MultiFixS {E Ts} (funs : MultiFixBodies E Ts) : specFuns E Ts :=
  joinSpecFuns
    (Fx_MkFuns
       (fun ixs => specFunsToMultiInterp (applyArrowSpecFuns funs (funIxsToSpecFuns ixs)))
       (fun ixs => Fx_Ret (funIxsToSpecFuns ixs))).

Definition LetRecS {E Ts A}
  (funs : MultiFixBodies E Ts) (body : arrowSpecFuns E Ts (SpecM E A)) : SpecM E A :=
  applyArrowSpecFuns body (MultiFixS funs).

End SpecM.
