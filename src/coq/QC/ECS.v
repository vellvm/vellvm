(* Heavily inspired by https://reasonablypolymorphic.com/blog/why-take-ecstasy/index.html *)

From Coq Require Import List.
From Ltac2 Require Import Ltac2.
Require Import ZArith String.
From Vellvm.Utils Require Import
  IntMaps
  Monads
  Default.

From Vellvm.QC Require Import Lens.
Import LensNotations.
Local Open Scope lens.

Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Data.Monads.ReaderMonad.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Structures.Foldable.
Require Import ExtLib.Structures.MonadPlus.
Import MonadNotation.
Import MonadPlusNotation.
Import ApplicativeNotation.
Import FunctorNotation.
Import ListNotations.

Definition Position := (Z * Z)%type.

Variant ComponentType :=
  | Field
  | Unique.

Variant StorageType :=
  | FieldOf
  | WorldOf : (Type -> Type) -> StorageType
  | SetterOf.

Variant Update (a : Type) :=
  | Keep
  | Unset
  | SetValue : a -> Update a.

#[global] Instance Default_Update {a} : Default (Update a).
split.
apply Keep.
Defined.

#[global] Instance Functor_Update : Functor Update.
split.
intros A B f ua.
destruct ua eqn:Hua.
- apply Keep.
- apply Unset.
- apply (SetValue _ (f a)).
Defined.

(* TODO: Move to intmap library *)
#[global] Instance Functor_IntMap : Functor IntMap.
split.
intros A B f ma.
eapply IntMaps.IM.map. apply f.
apply ma.
Defined.

(* TODO: Move to intmap library *)
#[global] Instance Functor_IntMapRaw : Functor IM.Raw.t.
split.
intros A B f ma.
eapply IM.Raw.map. apply f.
apply ma.
Defined.


Record Ent := mkEnt { unEnt : Z }.

Definition Component (s : StorageType) (c : ComponentType) (a : Type) : Type :=
  match s with
  | FieldOf => option a
  | SetterOf => Update a
  | WorldOf m =>
      match c with
      | Field => IM.Raw.t a
      | Unique => option (Z * a)
      end
  end.

#[global] Instance Functor_Component {s c} : Functor (Component s c).
split.
intros A B f.
destruct s.
- apply (fmap f).
- destruct c; cbn.
  + apply (fmap f).
  + intros o.
    destruct o eqn:Ho.
    * destruct p.
      apply (Some (z, f a)).
    * apply None.
- cbn.
  apply (fmap f).
Defined.

Record SystemState w m :=
  mkSystemState
  { systemStateNextEnt : Z
  ; systemStateEntities : IS.t
  ; systemStateMetadata : w (WorldOf m)
  }.

#[global] Instance Default_IntSet : Default IS.t
  := { def := IS.empty }.

#[global] Instance Default_IntMapRaw {e} : Default (@IM.Raw.t e)
  := { def := IM.Raw.empty _ }.

#[global] Instance Default_SystemState {w m} `{Default (w (WorldOf m))} : Default (SystemState w m)
  := { def := mkSystemState w m def def def }.

Class EntityStore (Store : Type) : Type := 
  { nextEnt : Lens' Store Z
  ; entities : Lens' Store IS.t
  }.

Definition nextEntSystem {w m} : Lens' (SystemState w m) Z.
  red.
  intros f F afa w'.

  refine
    open_constr:
      ((fun x => _) <$> afa (_ w')); try typeclasses_eauto.
  - constructor;
      Control.dispatch
        [ (fun _ => apply x)
          ; (fun _ => eapply systemStateEntities)
          ; (fun _ => eapply systemStateMetadata)
        ];
      apply w'.
  - intros w''.
    destruct w''.
    apply systemStateNextEnt0.
Defined.

Definition entitiesSystem {w m} : Lens' (SystemState w m) IS.t.
  red.
  intros f F afa w'.

  refine
    open_constr:
      ((fun x => _) <$> afa (_ w')); try typeclasses_eauto.
  - constructor;
      Control.dispatch
        [ (fun _ => eapply systemStateNextEnt)
          ; (fun _ => eapply x)
          ; (fun _ => eapply systemStateMetadata)
        ];
      apply w'.
  - intros w''.
    destruct w''.
    apply systemStateEntities0.
Defined.

#[global] Instance EntityStore_SystemState {w m} : EntityStore (SystemState w m).
split.
apply nextEntSystem.
apply entitiesSystem.
Defined.

Class MetadataStore {m} (Meta : StorageType -> Type) (Store : Type) : Type :=
  { metadata : Lens' Store (Meta (WorldOf m))
  }.

#[global] Instance MetadataStore_SystemState {w m} : @MetadataStore m w (SystemState w m).
split.
red.
intros f F afa w'.

refine
  open_constr:
    ((fun x => _) <$> afa (_ w')); try typeclasses_eauto.
- constructor;
    Control.dispatch
      [ (fun _ => eapply systemStateNextEnt)
        ; (fun _ => eapply systemStateEntities)
        ; (fun _ => eapply x)
      ];
    apply w'.
- intros w''.
  destruct w''.
  apply systemStateMetadata0.
Defined.

Definition SystemT W M A := stateT (SystemState W M) M A.
#[global] Instance Monad_SystemT {w} {m} `{Monad m} : Monad (SystemT w m).
unfold SystemT.
apply Monad_stateT; auto.
Defined.

#[global] Instance MonadState_SystemT {w} {m} `{Monad m} : MonadState (SystemState w m) (SystemT w m).
unfold SystemT.
apply MonadState_stateT; auto.
Defined.

#[global] Instance MonadT_SystemT {w} {m} `{Monad m} : MonadT (SystemT w m) m.
unfold SystemT.
apply MonadT_stateT; auto.
Defined.

Definition updateIntMap {a} (u : Update a) k (m : IntMap a) : IntMap a
  := match u with
     | Keep => m
     | Unset => delete k m
     | SetValue x => add k x m
     end.

Definition updateIntMapRaw {a} (u : Update a) k (m : IM.Raw.t a) : IM.Raw.t a
  := match u with
     | Keep => m
     | Unset => IM.Raw.remove k m
     | SetValue x => IM.Raw.add k x m
     end.

Definition optionToUpdate {a} (v : option a) : Update a :=
  match v with
  | Some x => SetValue _ x
  | None => Keep _
  end.

#[global] Instance Traversable_option : Traversable option.
split.
intros F Ap A B X X0.
destruct X0 eqn:Hx.
- apply (Some <$> X a).
- apply (pure None).
Defined.

#[global] Instance Traversable_Update : Traversable Update.
split.
intros F Ap A B X X0.
destruct X0 eqn:Hx.
- apply (pure (Keep _)).
- apply (pure (Unset _)).
- apply (SetValue _ <$> X a).
Defined.

#[global] Instance Traversable_Component {s c} : Traversable (Component s c).
split.
intros F Ap A B X X0.
destruct s; cbn in *.
- eapply mapT; eauto.
- destruct c.
  + eapply mapT; eauto.
  + eapply mapT.
    2: apply X0.
    intros X1.
    eapply ap.
    2: apply (X (snd X1)).
    apply (pure (fun b => (fst X1, b))).
- eapply mapT; eauto.
Defined.

Definition optSetMap {a} (mv : option a) k (m : IntMap a) : IntMap a
  := match mv with
     | Some v => add k v m
     | None => delete k m
     end.

Definition optSetMapRaw {a} (mv : option a) k (m : IM.Raw.t a) : IM.Raw.t a
  := match mv with
     | Some v => IM.Raw.add k v m
     | None => IM.Raw.remove k m
     end.

Definition newEntity {w} {m} `{Monad m} : SystemT w m Ent
  := i <- use nextEnt;;
     nextEnt .= Z.succ i;;
     entities %= (fun ents => IS.add i ents);;
     ret (mkEnt i).

Definition runSystemT {w m} `{Default (w (WorldOf m))} `{Monad m} {a} (sys : SystemT w m a) : m a
  := evalStateT sys def.

Definition ixs {a} `{Default a} (ns : list nat) : Traversal (list a) (list a) a a.
  red.
  intros f F focus xs.
  refine constr:(let fix go (n : nat) (ns : list nat) (xs : list a) :=
            match xs with
            | nil => pure nil
            | cons a0 l =>
                let rest := go (S n) ns l in
                if (existsb (Nat.eqb n) ns)
                then (pure cons <*> focus a0 <*> rest)
                else (pure cons <*> pure a0 <*> rest)
            end
          in
          go 0 ns xs).
Defined.

Record QueryT w m a : Type :=
  mkQueryT
  { runQueryT' : readerT (Ent * w FieldOf) (optionT m) a
  }.

Arguments runQueryT' {_ _ _}.

#[global] Instance Monad_QueryT {w m} `{Monad m} : Monad (QueryT w m).
split.
- intros t X.
  apply mkQueryT.
  apply (ret X).
- intros A B qa k.
  apply mkQueryT.
  eapply bind.
  apply qa.
  apply k.
Defined.

#[global] Instance MonadZero_QueryT {w m} `{Monad m} : MonadZero (QueryT w m).
split.
intros T.
apply mkQueryT.
apply mzero.
Defined.

Definition unQueryT {w m a} (q : QueryT w m a)  (e : Ent) (meta : w FieldOf) : m (option a)
  := unOptionT (runReaderT (runQueryT' q) (e, meta)).

Definition query {world a m} `{Monad m} (f : world FieldOf -> option a) : QueryT world m a
  := e <- @mkQueryT world m _ (asks snd);;
     match f e with
     | None => mzero
     | Some x => ret x
     end.

Definition queryl {world a m} `{Monad m} (l : Lens' (world FieldOf) (Component FieldOf Field a)) : QueryT world m a
  := query (view l).

Definition withq {world a m} `{Monad m} (f : world FieldOf -> option a) : QueryT world m unit
  := query f;;
     ret tt.

Definition withl {world a m} `{Monad m} (l : Lens' (world FieldOf) (Component FieldOf Field a)) : QueryT world m unit
  := withq (view l).

Definition without {world a m} `{Monad m} (f : world FieldOf -> option a) : QueryT world m unit
  := e <- @mkQueryT world m _ (asks snd);;
     match f e with
     | None => ret tt
     | Some x => mzero
     end.

Definition withoutl {world a m} `{Monad m} (l : Lens' (world FieldOf) (Component FieldOf Field a)) : QueryT world m unit
  := without (view l).

(* I want to be able to use `IS.t` and `IM.Raw.t unit` and maybe `list Z` and `list Ent` as targets... What do I need from an EntTarget? *)
Class ToEnt T :=
  { toEnt : T -> Ent
  }.

#[global] Instance ToEnt_Z : ToEnt Z :=
  { toEnt := mkEnt }.

#[global] Instance ToEnt_Ent : ToEnt Ent :=
  { toEnt := id }.

Definition EntTarget {es E} `{ToEnt E} `{Foldable es E} w m := SystemT w m es.

Definition allEnts {w m} `{Monad m} : EntTarget w m (es:=IS.t)
  := use entities.
