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

Record Metadata s :=
  mkMetadata
    { name : Component s Field ident
    ; type_alias : Component s Field typ
    ; variable_type : Component s Field typ
    ; is_local : Component s Field unit
    ; is_global : Component s Field unit
    ; is_non_deterministic : Component s Field unit
    (* Whether the variable is the result of a pointer cast *)
    ; from_pointer : Component s Field Ent
    (* Whether the variable has a pointer type *)
    ; is_pointer : Component s Field unit
    (* Whether the variable is a pointer to sized type *)
    ; is_sized_pointer : Component s Field unit
    (* Whether the variable is of a sized type *)
    ; is_sized : Component s Field unit
    (* Whether the variable is an aggregate type *)
    ; is_aggregate : Component s Field unit
    (* Whether the variable is a vector type *)
    ; is_vector : Component s Field unit
    (* Whether the variable is an array type *)
    ; is_array : Component s Field unit
    (* Whether the variable is a structure type *)
    ; is_struct : Component s Field unit
    (* Whether the variable is a void type *)
    ; is_non_void : Component s Field unit
    (* Whether the variable is a pointer type or a vector of pointers *)
    ; is_ptr_vector : Component s Field unit
    (* Whether the variable is a pointer type or a vector of pointers to sized types *)
    ; is_sized_ptr_vector : Component s Field unit
    (* Whether a type alias is to a sized type *)
    ; is_sized_type_alias : Component s Field unit
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
  ; (fun _ => apply is_pointer)
  ; (fun _ => apply is_sized_pointer)
  ; (fun _ => apply is_sized)
  ; (fun _ => apply is_aggregate)
  ; (fun _ => apply is_vector)
  ; (fun _ => apply is_array)
  ; (fun _ => apply is_struct)
  ; (fun _ => apply is_non_void)
  ; (fun _ => apply is_ptr_vector)
  ; (fun _ => apply is_sized_ptr_vector)
  ; (fun _ => apply is_sized_type_alias)
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
      ; (fun _ => tac (); apply is_pointer)
      ; (fun _ => tac (); apply is_sized_pointer)
      ; (fun _ => tac (); apply is_sized)
      ; (fun _ => tac (); apply is_aggregate)
      ; (fun _ => tac (); apply is_vector)
      ; (fun _ => tac (); apply is_array)
      ; (fun _ => tac (); apply is_struct)
      ; (fun _ => tac (); apply is_non_void)
      ; (fun _ => tac (); apply is_ptr_vector)
      ; (fun _ => tac (); apply is_sized_ptr_vector)
      ; (fun _ => tac (); apply is_sized_type_alias)
    ].

Definition getEntity {w m} `{Monad m} `{@MetadataStore m Metadata (SystemState w m)}
  (entity : Ent) : SystemT w m (Metadata FieldOf).
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

Definition optionToUpdate {a} (v : option a) : Update a :=
  match v with
  | Some x => SetValue _ x
  | None => Keep _
  end.

Definition setterOfFields (vals : Metadata FieldOf) : Metadata SetterOf.
  constructor;
    applyMetadataConstructors (fun _ => refine open_constr:(optionToUpdate (_ vals))).
Defined.

Definition setEntity
  {w m} `{Monad m} `{@MetadataStore m Metadata (SystemState w m)}
  (entity : Ent) (setter : Metadata SetterOf) : SystemT w m unit.
  refine
    open_constr:(let entity_id := unEnt entity in
                 metadata _ _ %= (fun storage => _);;
                 entities %= (fun ents => IS.add entity_id ents);;
                 ret tt);
    try typeclasses_eauto.
  apply (mkMetadata (WorldOf m));
    applyMetadataConstructors (fun _ => refine open_constr:(updateIntMapRaw (_ setter) entity_id (_ storage))).
Defined.

Definition setEntities
  {w : StorageType -> Type} {m : Type -> Type}
  `{Monad m} `{@MetadataStore m Metadata (SystemState w m)}
  (es : IM.Raw.t (Metadata FieldOf)) : SystemT w m unit
  := IM.Raw.fold (fun k fs acc => setEntity (mkEnt k) (setterOfFields fs);; acc) es (ret tt).

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
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
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
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
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
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
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
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
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
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
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
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
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
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
        ];
      apply w.
  - apply from_pointer.
Defined.

Definition is_pointer' {s : StorageType} : Lens' (Metadata s) (Component s Field unit).
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
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply x)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
        ];
      apply w.
  - apply is_pointer.
Defined.

Definition is_sized_pointer' {s : StorageType} : Lens' (Metadata s) (Component s Field unit).
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
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply x)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
        ];
      apply w.
  - apply is_sized_pointer.
Defined.

Definition is_sized' {s : StorageType} : Lens' (Metadata s) (Component s Field unit).
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
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply x)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
        ];
      apply w.
  - apply is_sized.
Defined.

Definition is_aggregate' {s : StorageType} : Lens' (Metadata s) (Component s Field unit).
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
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply x)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
        ];
      apply w.
  - apply is_aggregate.
Defined.

Definition is_vector' {s : StorageType} : Lens' (Metadata s) (Component s Field unit).
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
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply x)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
        ];
      apply w.
  - apply is_vector.
Defined.

Definition is_array' {s : StorageType} : Lens' (Metadata s) (Component s Field unit).
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
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply x)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
        ];
      apply w.
  - apply is_array.
Defined.

Definition is_struct' {s : StorageType} : Lens' (Metadata s) (Component s Field unit).
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
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply x)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
        ];
      apply w.
  - apply is_struct.
Defined.

Definition is_non_void' {s : StorageType} : Lens' (Metadata s) (Component s Field unit).
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
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply x)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
        ];
      apply w.
  - apply is_non_void.
Defined.

Definition is_ptr_vector' {s : StorageType} : Lens' (Metadata s) (Component s Field unit).
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
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply x)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
        ];
      apply w.
  - apply is_ptr_vector.
Defined.

Definition is_sized_ptr_vector' {s : StorageType} : Lens' (Metadata s) (Component s Field unit).
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
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply x)
          ; (fun _ => apply is_sized_type_alias)
        ];
      apply w.
  - apply is_sized_ptr_vector.
Defined.

Definition is_sized_type_alias' {s : StorageType} : Lens' (Metadata s) (Component s Field unit).
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
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply x)
        ];
      apply w.
  - apply is_sized_type_alias.
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
     nextEnt .= Z.succ i;;
     entities %= (fun ents => IS.add i ents);;
     ret (mkEnt i).

Definition deleteEntity {w} {m} `{Monad m} `{@MetadataStore m Metadata (SystemState w m)} (e : Ent) : SystemT w m unit
  := let eid := unEnt e in
     metadata .@ entl e .= def;;
     entities %= (fun ents => IS.remove eid ents);;
     ret tt.

Definition deleteEntities
  {w : StorageType -> Type} {m : Type -> Type}
  `{Monad m} `{@MetadataStore m Metadata (SystemState w m)} {A}
  (es : IM.Raw.t A) : SystemT w m unit
  := IM.Raw.fold (fun k _ acc => deleteEntity (mkEnt k);; acc) es (ret tt).

Definition runSystemT {m} `{Monad m} {a} (w : Metadata (WorldOf m)) (sys : SystemT Metadata m a) : m a
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

Definition names'' {m} : Traversal (Metadata (WorldOf m)) (Metadata (WorldOf m)) (Component (WorldOf m) Field ident) (Component (WorldOf m) Field ident).
  red.
  intros f F focus meta.
  refine open_constr:(pure (mkMetadata (WorldOf m)) <*> _ <*> _ <*> _ <*> _ <*> _ <*> _ <*> _
                     <*> _ <*> _ <*> _ <*> _ <*> _ <*> _ <*> _ <*> _ <*> _ <*> _ <*> _);
    try typeclasses_eauto.
  - apply (focus (name _ meta)).
  - apply (pure (type_alias _ meta)).
  - apply (pure (variable_type _ meta)).
  - apply (pure (is_local _ meta)).
  - apply (pure (is_global _ meta)).
  - apply (pure (is_non_deterministic _ meta)).
  - apply (pure (from_pointer _ meta)).
  - apply (pure (is_pointer _ meta)).
  - apply (pure (is_sized_pointer _ meta)).
  - apply (pure (is_sized _ meta)).
  - apply (pure (is_aggregate _ meta)).
  - apply (pure (is_vector _ meta)).
  - apply (pure (is_array _ meta)).
  - apply (pure (is_struct _ meta)).
  - apply (pure (is_non_void _ meta)).
  - apply (pure (is_ptr_vector _ meta)).
  - apply (pure (is_sized_ptr_vector _ meta)).
  - apply (pure (is_sized_type_alias _ meta)).
Defined.

Record QueryT w m a : Type :=
  mkQueryT
  { runQueryT' :: readerT (Ent * w FieldOf) (optionT m) a
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

Definition without {world a m} `{MonadZero m} `{Monad m} (f : world FieldOf -> option a) : QueryT world m unit
  := e <- @mkQueryT world m _ (asks snd);;
     match f e with
     | None => ret tt
     | Some x => mzero
     end.

Definition withoutl {world a m} `{MonadZero m} `{Monad m} (l : Lens' (world FieldOf) (Component FieldOf Field a)) : QueryT world m unit
  := without (view l).

(* I want to be able to use `IS.t` and `IM.Raw.t unit` and maybe `list Z` and `list Ent` as targets... What do I need from an EntTarget? *)
Class ToEnt T :=
  { toEnt : T -> Ent
  }.

#[global] Instance ToEnt_Z : ToEnt Z :=
  { toEnt := mkEnt }.

#[global] Instance ToEnt_Ent : ToEnt Ent :=
  { toEnt := id }.

Import Monoid.
#[global] Instance Foldable_IS : Foldable IS.t Z.
split.
intros m M conv s.
apply (IS.fold (fun k acc => monoid_plus M (conv k) acc) s (monoid_unit M)).
Defined.

#[global] Instance Foldable_list {a} : Foldable (list a) a.
split.
intros m M conv l.
apply (fold_left (fun acc x => monoid_plus M (conv x) acc) l (monoid_unit M)).
Defined.

Definition EntTarget {es E} `{ToEnt E} `{Foldable es E} w m := SystemT w m es.

Definition allEnts {w m} `{Monad m} : EntTarget w m (es:=IS.t)
  := use entities.

Definition emap
  {w m} `{Monad m} `{@MetadataStore m Metadata (SystemState w m)}
  {es E} `{ToEnt E} `{Foldable es E}
  (t : EntTarget w m (E:=E)) (q : QueryT Metadata m (Metadata SetterOf)) : SystemT w m unit
  := es <- t;;
     fold _
       (fun (k : E) (acc : SystemT w m unit) =>
          let e := toEnt k in
          meta <- getEntity e;;
          sets <- lift (unQueryT q e meta);;
          match sets with
          | None =>
              acc
          | Some s =>
              setEntity e s;;
              acc
          end
       ) (ret tt) es.

(* Filter out Nones from a set of options *)
Class FilterNone T :=
  { filterNone : forall {a}, T (option a) -> T a }.

#[global] Instance FilterNone_list : FilterNone list :=
  { filterNone _ l := fold_right (fun x acc => match x with | None => acc | Some x => x :: acc end) [] l }.

Program Definition efor
  {w m} `{Monad m} `{@MetadataStore m Metadata (SystemState w m)}
  {a}
  (t : @EntTarget (list Ent) Ent _ _ w m) (q : QueryT Metadata m a) : SystemT w m (list a)
  := es <- t;;
     _.
Next Obligation.
  refine open_constr:(fmap filterNone _);
    try typeclasses_eauto.
  refine open_constr:((fun a b => mapT b a) es (fun e => cs <- getEntity (toEnt e);; lift (unQueryT q e cs)));
    try typeclasses_eauto.
Defined.

Definition add_global {m} `{Monad m} (name : string) : SystemT Metadata m _
  := e <- newEntity;;
     metadata .@ entl e .@ is_global' .= ret tt;;
     metadata .@ entl e .@ name' .= ret (ID_Global (Name name));;
     ret e.

Definition add_local {m} `{Monad m} (name : string) : SystemT Metadata m _
  := e <- newEntity;;
     metadata .@ entl e .@ is_local' .= ret tt;;
     metadata .@ entl e .@ name' .= ret (ID_Local (Name name));;
     ret e.

Definition test_system {m} `{HM: Monad m} : SystemT Metadata m _
  := e <- newEntity;;
     e2 <- newEntity;;
     add_global "blah";;
     add_global "wee";;
     add_local "foo";;
     emap allEnts
       (n <- query (name FieldOf);;
        withq (is_global FieldOf);;
        ret (def & @name' SetterOf .~ SetValue _ (ID_Global (Name "ueoaue"))));;
     get.

Definition ecs_test :=
  IdentityMonad.unIdent (runSystemT def test_system).

(* What if I want to find an entity that's not in the set? *)
Eval compute in ecs_test.
