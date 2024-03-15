From Coq Require Import List.
From Ltac2 Require Import Ltac2.
Require Import ZArith String.
From Vellvm.Utils Require Import
  IntMaps
  Monads
  Default.

From Vellvm.Syntax Require Import
  LLVMAst.

From Vellvm.QC Require Import Lens.
Import LensNotations.
Local Open Scope lens.

Require Import ExtLib.Data.Monads.StateMonad.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Traversable.
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

Record Metadata s :=
  mkMetadata
    { name : Component s Field ident
    ; type_alias : Component s Field typ
    ; variable_type : Component s Field typ
    ; is_local : Component s Field unit
    ; is_global : Component s Field unit
    ; is_non_deterministic : Component s Field unit
    ; from_pointer : Component s Field Ent
    }.

Definition blankSetter : (Metadata SetterOf).
  constructor.
  all: apply Keep.
Defined.

Definition defFields : (Metadata FieldOf).
  constructor.
  all: apply None.
Defined.

#[global] Instance Default_Metadata {s} : Default (Metadata s).
split.
destruct s.
- apply defFields.
- apply mkMetadata; apply IM.empty.
- apply blankSetter.
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

Class MetadataStore {m} (Meta : _) (Store : Type) : Type :=
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

Ltac2 metadataConstructors :=
  [ (fun _ => apply name)
  ; (fun _ => apply type_alias)
  ; (fun _ => apply variable_type)
  ; (fun _ => apply is_local)
  ; (fun _ => apply is_global)
  ; (fun _ => apply is_non_deterministic)
  ; (fun _ => apply from_pointer)
  ].

Ltac2 applyMetadataConstructors (tac : unit -> unit) :=
  Control.dispatch
    [ (fun _ => tac (); apply name)
      ; (fun _ => tac (); apply type_alias)
      ; (fun _ => tac (); apply variable_type)
      ; (fun _ => tac (); apply is_local)
      ; (fun _ => tac (); apply is_global)
      ; (fun _ => tac (); apply is_non_deterministic)
      ; (fun _ => tac (); apply from_pointer)
    ].  

Definition getEntity {m} `{Monad m} (entity : Ent) : SystemT Metadata m (Metadata FieldOf).
  refine open_constr:(let entity_id := unEnt entity in
                      storage <- use metadata;;
                      ret (_)); try typeclasses_eauto.
  apply (mkMetadata FieldOf);
    refine open_constr:(IM.Raw.find entity_id (_ storage));
    Control.dispatch metadataConstructors.
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

Definition setEntity
  {m} `{Monad m} (entity : Ent) (setter : Metadata SetterOf) : SystemT Metadata m unit.
  refine
    open_constr:(let entity_id := unEnt entity in
                 metadata _ _ %= (fun storage => _);;
                 ret tt);
    try typeclasses_eauto.
  apply (mkMetadata (WorldOf m));
    applyMetadataConstructors (fun _ => refine open_constr:(updateIntMapRaw (_ setter) entity_id (_ storage))).
Defined.

Definition name' {s : StorageType} : Lens' (Metadata s) (Component s Field ident).
  red.
  intros f F afa w.
  refine open_constr:((fun x => _) <$> afa (_ w)); try typeclasses_eauto.
  - apply mkMetadata;
      Control.dispatch
        [ (fun _ => apply x)
          ; (fun _ => apply type_alias)
          ; (fun _ => apply variable_type)
          ; (fun _ => apply is_local)
          ; (fun _ => apply is_global)
          ; (fun _ => apply is_non_deterministic)
          ; (fun _ => apply from_pointer)
        ];
      apply w.
  - apply name.
Defined.

Definition is_global' {s : StorageType} : Lens' (Metadata s) (Component s Field unit).
  red.
  intros f F afa w.
  refine open_constr:((fun x => _) <$> afa (_ w)); try typeclasses_eauto.
  - apply mkMetadata;
      Control.dispatch
        [ (fun _ => apply name)
          ; (fun _ => apply type_alias)
          ; (fun _ => apply variable_type)
          ; (fun _ => apply is_local)
          ; (fun _ => apply x)
          ; (fun _ => apply is_non_deterministic)
          ; (fun _ => apply from_pointer)
        ];
      apply w.
  - apply is_global.
Defined.

Definition is_local' {s : StorageType} : Lens' (Metadata s) (Component s Field unit).
  red.
  intros f F afa w.
  refine open_constr:((fun x => _) <$> afa (_ w)); try typeclasses_eauto.
  - apply mkMetadata;
      Control.dispatch
        [ (fun _ => apply name)
          ; (fun _ => apply type_alias)
          ; (fun _ => apply variable_type)
          ; (fun _ => apply x)
          ; (fun _ => apply is_global)
          ; (fun _ => apply is_non_deterministic)
          ; (fun _ => apply from_pointer)
        ];
      apply w.
  - apply is_local.
Defined.

Definition type_alias' {s : StorageType} : Lens' (Metadata s) (Component s Field typ).
  red.
  intros f F afa w.
  refine open_constr:((fun x => _) <$> afa (_ w)); try typeclasses_eauto.
  - apply mkMetadata;
      Control.dispatch
        [ (fun _ => apply name)
          ; (fun _ => apply x)
          ; (fun _ => apply variable_type)
          ; (fun _ => apply is_local)
          ; (fun _ => apply is_global)
          ; (fun _ => apply is_non_deterministic)
          ; (fun _ => apply from_pointer)
        ];
      apply w.
  - apply type_alias.
Defined.

Definition variable_type' {s : StorageType} : Lens' (Metadata s) (Component s Field typ).
  red.
  intros f F afa w.
  refine open_constr:((fun x => _) <$> afa (_ w)); try typeclasses_eauto.
  - apply mkMetadata;
      Control.dispatch
        [ (fun _ => apply name)
          ; (fun _ => apply type_alias)
          ; (fun _ => apply x)
          ; (fun _ => apply is_local)
          ; (fun _ => apply is_global)
          ; (fun _ => apply is_non_deterministic)
          ; (fun _ => apply from_pointer)
        ];
      apply w.
  - apply type_alias.
Defined.

Definition is_non_deterministic' {s : StorageType} : Lens' (Metadata s) (Component s Field unit).
  red.
  intros f F afa w.
  refine open_constr:((fun x => _) <$> afa (_ w)); try typeclasses_eauto.
  - apply mkMetadata;
      Control.dispatch
        [ (fun _ => apply name)
          ; (fun _ => apply type_alias)
          ; (fun _ => apply variable_type)
          ; (fun _ => apply is_local)
          ; (fun _ => apply is_global)
          ; (fun _ => apply x)
          ; (fun _ => apply from_pointer)
        ];
      apply w.
  - apply is_non_deterministic.
Defined.

Definition from_pointer' {s : StorageType} : Lens' (Metadata s) (Component s Field Ent).
  red.
  intros f F afa w.
  refine open_constr:((fun x => _) <$> afa (_ w)); try typeclasses_eauto.
  - apply mkMetadata;
      Control.dispatch
        [ (fun _ => apply name)
          ; (fun _ => apply type_alias)
          ; (fun _ => apply variable_type)
          ; (fun _ => apply is_local)
          ; (fun _ => apply is_global)
          ; (fun _ => apply is_non_deterministic)
          ; (fun _ => apply x)
        ];
      apply w.
  - apply from_pointer.
Defined.

Definition ident_to_raw_id (i : ident) :=
  match i with
  | ID_Global id => id
  | ID_Local id => id
  end.

(* Merge taking the latter arguments' values if duplicates.
   Unclear if IM.Raw.merge would have this property.
 *)
Definition IM_merge {a} (m1 : IM.Raw.t a) (m2 : IM.Raw.t a) : IM.Raw.t a
  := IM.Raw.fold (IM.Raw.add (elt:=a)) m2 m1.

(* (* Virtual lens for setting global identifiers *) *)
(* Definition global' {s : StorageType} : Lens' (Metadata s) (Component s Field Ent). *)
(*   red. *)
(*   intros f F afa w. *)
(*   refine open_constr:((fun x => _) <$> afa (_ w)); try typeclasses_eauto. *)
(*   - apply mkMetadata; *)
(*       Control.dispatch *)
(*         [ (fun _ => apply name) *)
(*           ; (fun _ => apply type_alias) *)
(*           ; (fun _ => apply variable_type) *)
(*           ; (fun _ => apply is_local) *)
(*           ; (fun _ => apply (fmap (fun _ => tt) x)) *)
(*           ; (fun _ => apply is_non_deterministic) *)
(*           ; (fun _ => apply from_pointer) *)
(*         ]; *)
(*       apply w. *)
(*   - intros w'. *)
(*     apply (global _ w). *)
(*     apply (fmap ident_to_raw_id (name _ w')). *)
(* Defined. *)

(* Definition globals' {m} (w : Metadata (WorldOf m)) : list Ent. *)
(*   apply is_global in w. *)
(*   red in w. *)
(*   apply (fmap (fun e => mkEnt (fst e)) (IM.Raw.elements w)). *)
(* Defined. *)

(* Definition local' {m} : Lens' (Metadata (WorldOf m)) (Component (WorldOf m) Field raw_id). *)
(*   red. *)
(*   intros f F afa w. *)
(*   refine open_constr:((fun x => _) <$> afa (_ w)); try typeclasses_eauto. *)
(*   - apply mkMetadata; *)
(*       Control.dispatch *)
(*         [ (fun _ => apply (IM.Raw.fold (IM.Raw.add (elt:=ident)) (fmap (fun g => ID_Local g) x) (name _ w))) *)
(*           ; (fun _ => apply type_alias) *)
(*           ; (fun _ => apply variable_type) *)
(*           ; (fun _ => apply (fmap (fun _ => tt) x)) *)
(*           ; (fun _ => apply is_global) *)
(*           ; (fun _ => apply is_non_deterministic) *)
(*           ; (fun _ => apply from_pointer) *)
(*         ]; *)
(*       apply w. *)
(*   - intros w'. *)
(*     apply (fmap ident_to_raw_id (name _ w')). *)
(* Defined. *)

(* Definition type_alias' {m} : Lens' (Metadata (WorldOf m)) (Component (WorldOf m) Field raw_id * Component (WorldOf m) Field typ). *)
(*   red. *)
(*   intros f F afa w. *)
(*   refine open_constr:((fun x => _) <$> afa (_ w)); try typeclasses_eauto. *)
(*   - apply mkMetadata; *)
(*       Control.dispatch *)
(*         [ (fun _ => apply (IM.Raw.fold (IM.Raw.add (elt:=ident)) (fmap (fun g => ID_Global g) (fst x)) (name _ w))) *)
(*           ; (fun _ => apply (snd x)) *)
(*           ; (fun _ => apply variable_type) *)
(*           ; (fun _ => apply is_local) *)
(*           ; (fun _ => apply is_global) *)
(*           ; (fun _ => apply is_non_deterministic) *)
(*           ; (fun _ => apply from_pointer) *)
(*         ]; *)
(*       apply w. *)
(*   - intros w'. *)
(*     apply (fmap ident_to_raw_id (name _ w'), (type_alias _ w')). *)
(* Defined. *)

(* Definition from_pointer' {m} : Lens' (Metadata (WorldOf m)) (Component (WorldOf m) Field Ent). *)
(*   red. *)
(*   intros f F afa w. *)
(*   refine open_constr:((fun x => _) <$> afa (_ w)); try typeclasses_eauto. *)
(*   - apply mkMetadata; *)
(*       Control.dispatch *)
(*         [ (fun _ => apply name) *)
(*           ; (fun _ => apply type_alias) *)
(*           ; (fun _ => apply variable_type) *)
(*           ; (fun _ => apply is_local) *)
(*           ; (fun _ => apply is_global) *)
(*           ; (fun _ => apply is_non_deterministic) *)
(*           ; (fun _ => apply (IM.Raw.fold (IM.Raw.add (elt:=Ent)) x (from_pointer _ w))) *)
(*         ]; *)
(*       apply w. *)
(*   - intros w'. *)
(*     apply (from_pointer _ w'). *)
(* Defined. *)

Definition traverseWithKeyRaw {t} `{Applicative t} {a b} (f : IM.Raw.key -> a -> t b) (m : IM.Raw.t a) : t (IM.Raw.t b)
  :=
  let fix go x :=
    match x with
    | IM.Raw.Leaf => pure (IM.Raw.Leaf _)
    | IM.Raw.Node l k v r h =>
        if Z.eqb 1%Z h
        then (fun v' => IM.Raw.Node (IM.Raw.Leaf _) k v' (IM.Raw.Leaf _) 1%Z) <$> f k v
        else (fun l' v' r' => IM.Raw.Node l' k v' r' h) <$> go l <*> f k v <*> go r
    end
  in
  go m.

#[global] Instance Traversable_RawIntMap : Traversable IM.Raw.t.
split.
intros F Ap A B X X0.
eapply traverseWithKeyRaw.
intros k.
apply X.
apply X0.
Defined.

Definition traverseWithKey {t} `{Applicative t} {a b} (f : IM.key -> a -> t b) (m : IM.t a) : t (IM.t b).
  eapply @IM.fold.
  3: apply (pure (IM.empty _)).
  2: apply m.
  - intros k e acc.
    refine open_constr:(let res := f k e in _).
    eapply ap.
    2: apply acc.
    eapply fmap.
    2: apply res.
    apply (IM.add k).
Defined.

#[global] Instance Traversable_IntMap : Traversable IntMap.
split.
intros F Ap A B X X0.
eapply traverseWithKey.
intros k.
apply X.
apply X0.
Defined.

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

Definition entl {m} `{HM: Monad m} (e : Ent) : Lens' (Metadata (WorldOf m)) (Metadata FieldOf).
  red.
  intros f F afa w.

  refine
    open_constr:
      (let eid := unEnt e in
       ((fun x => _) <$> afa (_ w))); try typeclasses_eauto.
  - apply mkMetadata; red;
      applyMetadataConstructors (fun _ => refine open_constr:(optSetMapRaw (_ x) eid (_ w))).
  - intros w'.
    apply (mkMetadata FieldOf);
      refine open_constr:(IM.Raw.find eid (_ w'));
      Control.dispatch metadataConstructors.
Defined.

Definition newEntity {w} {m} `{Monad m} : SystemT w m Ent
  := i <- use nextEnt;;
     nextEnt _ _ .= Z.succ i;;
     entities _ _ %= (fun ents => IS.add i ents);;
     ret (mkEnt i).

Definition deleteEntity {w} {m} `{Monad m} `{@MetadataStore m Metadata (SystemState w m)} (e : Ent) : SystemT w m unit
  := let eid := unEnt e in
     (metadata .@ entl e) _ _ .= def;;
     entities _ _ %= (fun ents => IS.remove eid ents);;
     ret tt.

Definition runSystemT {m} `{Monad m} {a} (w : Metadata (WorldOf m)) (sys : SystemT Metadata m a) : m a
  := evalStateT sys def.

Definition add_global {m} `{Monad m} (name : string) : SystemT Metadata m _
  := e <- newEntity;;
     (metadata .@ entl e .@ is_global') _ _ .= ret tt;;
     (metadata .@ entl e .@ name') _ _ .= ret (ID_Global (Name name));;
     ret e.

Definition add_local {m} `{Monad m} (name : string) : SystemT Metadata m _
  := e <- newEntity;;
     (metadata .@ entl e .@ is_local') _ _ .= ret tt;;
     (metadata .@ entl e .@ name') _ _ .= ret (ID_Local (Name name));;
     ret e.

Definition test_system {m} `{HM: Monad m} : SystemT Metadata m _
  := e <- newEntity;;
     e2 <- newEntity;;
     add_global "blah";;
     add_local "foo";;
     get.

Definition ecs_test :=
  IdentityMonad.unIdent (runSystemT def test_system).

(* What if I want to find an entity that's not in the set? *)
Eval compute in ecs_test.

Definition firstAndThird {a x b} : Traversal (a * x * a) (b * x * b) a b.
  red.
  intros f F focus X0.
  destruct X0 as [[a' b'] c'].
  apply (pure (fun a b c => (a, b, c)) <*> focus a' <*> pure b' <*> focus c').
Defined.

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

Eval compute in (over (ixs [1; 4] _ _) (fun x => 2 * x) [1; 2; 3; 4; 5]).
Eval compute in (over (firstAndThird _ _) length ("one", 2, "three")).

Definition names'' {m} : Traversal (Metadata (WorldOf m)) (Metadata (WorldOf m)) (Component (WorldOf m) Field ident) (Component (WorldOf m) Field ident).
  red.
  intros f F focus meta.
  refine open_constr:(pure (mkMetadata (WorldOf m)) <*> _ <*> _ <*> _ <*> _ <*> _ <*> _ <*> _);
    try typeclasses_eauto.
  - apply (focus (name _ meta)).
  - apply (pure (type_alias _ meta)).
  - apply (pure (variable_type _ meta)).
  - apply (pure (is_local _ meta)).
  - apply (pure (is_global _ meta)).
  - apply (pure (is_non_deterministic _ meta)).
  - apply (pure (from_pointer _ meta)).
Defined.
