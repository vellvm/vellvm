From Ltac2 Require Import Ltac2.
From Coq Require Import List String.
From Vellvm.Utils Require Import
  IntMaps
  Monads
  Default.

From Vellvm.Syntax Require Import
  LLVMAst.

From Vellvm.QC Require Import ECS Lens.
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

Record Metadata s :=
  mkMetadata
    { name : Component s Field ident
    ; type_alias : Component s Field typ
    ; variable_type : Component s Field typ
    ; normalized_type : Component s Field typ
    ; is_local : Component s Field unit
    ; is_global : Component s Field unit
    ; is_deterministic : Component s Field unit
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
    (* Whether the variable is an aggregate type with values (e.g., not an array of 0 elements) *)
    ; is_indexable : Component s Field unit
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
    (* Whether a variable / type alias has a first class type *)
    ; is_first_class_type : Component s Field unit
    (* Whether a variable / type alias has a function pointer type *)
    ; is_function_pointer : Component s Field unit
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

Ltac2 metadataConstructors :=
  [ (fun _ => apply name)
  ; (fun _ => apply type_alias)
  ; (fun _ => apply variable_type)
  ; (fun _ => apply normalized_type)
  ; (fun _ => apply is_local)
  ; (fun _ => apply is_global)
  ; (fun _ => apply is_deterministic)
  ; (fun _ => apply is_non_deterministic)
  ; (fun _ => apply from_pointer)
  ; (fun _ => apply is_pointer)
  ; (fun _ => apply is_sized_pointer)
  ; (fun _ => apply is_sized)
  ; (fun _ => apply is_aggregate)
  ; (fun _ => apply is_indexable)
  ; (fun _ => apply is_vector)
  ; (fun _ => apply is_array)
  ; (fun _ => apply is_struct)
  ; (fun _ => apply is_non_void)
  ; (fun _ => apply is_ptr_vector)
  ; (fun _ => apply is_sized_ptr_vector)
  ; (fun _ => apply is_sized_type_alias)
  ; (fun _ => apply is_first_class_type)
  ; (fun _ => apply is_function_pointer)
  ].

Ltac2 applyMetadataConstructors (tac : unit -> unit) :=
  Control.dispatch
    [ (fun _ => tac (); apply name)
      ; (fun _ => tac (); apply type_alias)
      ; (fun _ => tac (); apply variable_type)
      ; (fun _ => tac (); apply normalized_type)
      ; (fun _ => tac (); apply is_local)
      ; (fun _ => tac (); apply is_global)
      ; (fun _ => tac (); apply is_deterministic)
      ; (fun _ => tac (); apply is_non_deterministic)
      ; (fun _ => tac (); apply from_pointer)
      ; (fun _ => tac (); apply is_pointer)
      ; (fun _ => tac (); apply is_sized_pointer)
      ; (fun _ => tac (); apply is_sized)
      ; (fun _ => tac (); apply is_aggregate)
      ; (fun _ => tac (); apply is_indexable)
      ; (fun _ => tac (); apply is_vector)
      ; (fun _ => tac (); apply is_array)
      ; (fun _ => tac (); apply is_struct)
      ; (fun _ => tac (); apply is_non_void)
      ; (fun _ => tac (); apply is_ptr_vector)
      ; (fun _ => tac (); apply is_sized_ptr_vector)
      ; (fun _ => tac (); apply is_sized_type_alias)
      ; (fun _ => tac (); apply is_first_class_type)
      ; (fun _ => tac (); apply is_function_pointer)
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
          ; (fun _ => apply normalized_type)
          ; (fun _ => apply is_local)
          ; (fun _ => apply is_global)
          ; (fun _ => apply is_deterministic)
          ; (fun _ => apply is_non_deterministic)
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_indexable)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
          ; (fun _ => apply is_first_class_type)
          ; (fun _ => apply is_function_pointer)
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
          ; (fun _ => apply normalized_type)
          ; (fun _ => apply is_local)
          ; (fun _ => apply x)
          ; (fun _ => apply is_deterministic)
          ; (fun _ => apply is_non_deterministic)
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_indexable)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
          ; (fun _ => apply is_first_class_type)
          ; (fun _ => apply is_function_pointer)
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
          ; (fun _ => apply normalized_type)
          ; (fun _ => apply x)
          ; (fun _ => apply is_global)
          ; (fun _ => apply is_deterministic)
          ; (fun _ => apply is_non_deterministic)
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_indexable)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
          ; (fun _ => apply is_first_class_type)
          ; (fun _ => apply is_function_pointer)
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
          ; (fun _ => apply normalized_type)
          ; (fun _ => apply is_local)
          ; (fun _ => apply is_global)
          ; (fun _ => apply is_deterministic)
          ; (fun _ => apply is_non_deterministic)
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_indexable)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
          ; (fun _ => apply is_first_class_type)
          ; (fun _ => apply is_function_pointer)
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
          ; (fun _ => apply normalized_type)
          ; (fun _ => apply is_local)
          ; (fun _ => apply is_global)
          ; (fun _ => apply is_deterministic)
          ; (fun _ => apply is_non_deterministic)
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_indexable)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
          ; (fun _ => apply is_first_class_type)
          ; (fun _ => apply is_function_pointer)
        ];
      apply w.
  - apply variable_type.
Defined.

Definition normalized_type' {s : StorageType} : Lens' (Metadata s) (Component s Field typ).
  red.
  intros f F afa w.
  refine open_constr:((fun x => _) <$> afa (_ w)); try typeclasses_eauto.
  - apply mkMetadata;
      Control.dispatch
        [ (fun _ => apply name)
          ; (fun _ => apply type_alias)
          ; (fun _ => apply variable_type)
          ; (fun _ => apply x)
          ; (fun _ => apply is_local)
          ; (fun _ => apply is_global)
          ; (fun _ => apply is_deterministic)
          ; (fun _ => apply is_non_deterministic)
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_indexable)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
          ; (fun _ => apply is_first_class_type)
          ; (fun _ => apply is_function_pointer)
        ];
      apply w.
  - apply normalized_type.
Defined.

Definition is_deterministic' {s : StorageType} : Lens' (Metadata s) (Component s Field unit).
  red.
  intros f F afa w.
  refine open_constr:((fun x => _) <$> afa (_ w)); try typeclasses_eauto.
  - apply mkMetadata;
      Control.dispatch
        [ (fun _ => apply name)
          ; (fun _ => apply type_alias)
          ; (fun _ => apply variable_type)
          ; (fun _ => apply normalized_type)
          ; (fun _ => apply is_local)
          ; (fun _ => apply is_global)
          ; (fun _ => apply x)
          ; (fun _ => apply is_non_deterministic)
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_indexable)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
          ; (fun _ => apply is_first_class_type)
          ; (fun _ => apply is_function_pointer)
        ];
      apply w.
  - apply is_deterministic.
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
          ; (fun _ => apply normalized_type)
          ; (fun _ => apply is_local)
          ; (fun _ => apply is_global)
          ; (fun _ => apply is_deterministic)
          ; (fun _ => apply x)
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_indexable)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
          ; (fun _ => apply is_first_class_type)
          ; (fun _ => apply is_function_pointer)
        ];
      apply w.
  - apply is_non_deterministic.
Defined.

Definition invert_option_unit (x : option unit) : option unit
  := match x with
     | Some _ => None
     | None => Some tt
     end.

Definition deterministic' : Lens' (Metadata FieldOf) bool.
  red.
  intros F HF f fields.
  ltac1:(pose proof (is_some (fields .^ is_deterministic')) as deterministicb).
  apply f in deterministicb.
  apply (fmap
           (fun (b : bool) =>
              if b
              then (fields
                    & @is_deterministic' FieldOf .~ ret tt
                    & @is_non_deterministic' FieldOf .~ None)
              else (fields
                    & @is_deterministic' FieldOf .~ None
                    & @is_non_deterministic' FieldOf .~ ret tt))).
  apply deterministicb.
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
          ; (fun _ => apply normalized_type)
          ; (fun _ => apply is_local)
          ; (fun _ => apply is_global)
          ; (fun _ => apply is_deterministic)
          ; (fun _ => apply is_non_deterministic)
          ; (fun _ => apply x)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_indexable)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
          ; (fun _ => apply is_first_class_type)
          ; (fun _ => apply is_function_pointer)
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
          ; (fun _ => apply normalized_type)
          ; (fun _ => apply is_local)
          ; (fun _ => apply is_global)
          ; (fun _ => apply is_deterministic)
          ; (fun _ => apply is_non_deterministic)
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply x)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_indexable)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
          ; (fun _ => apply is_first_class_type)
          ; (fun _ => apply is_function_pointer)
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
          ; (fun _ => apply normalized_type)
          ; (fun _ => apply is_local)
          ; (fun _ => apply is_global)
          ; (fun _ => apply is_deterministic)
          ; (fun _ => apply is_non_deterministic)
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply x)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_indexable)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
          ; (fun _ => apply is_first_class_type)
          ; (fun _ => apply is_function_pointer)
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
          ; (fun _ => apply normalized_type)
          ; (fun _ => apply is_local)
          ; (fun _ => apply is_global)
          ; (fun _ => apply is_deterministic)
          ; (fun _ => apply is_non_deterministic)
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply x)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_indexable)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
          ; (fun _ => apply is_first_class_type)
          ; (fun _ => apply is_function_pointer)
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
          ; (fun _ => apply normalized_type)
          ; (fun _ => apply is_local)
          ; (fun _ => apply is_global)
          ; (fun _ => apply is_deterministic)
          ; (fun _ => apply is_non_deterministic)
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply x)
          ; (fun _ => apply is_indexable)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
          ; (fun _ => apply is_first_class_type)
          ; (fun _ => apply is_function_pointer)
        ];
      apply w.
  - apply is_aggregate.
Defined.

Definition is_indexable' {s : StorageType} : Lens' (Metadata s) (Component s Field unit).
  red.
  intros f F afa w.
  refine open_constr:((fun x => _) <$> afa (_ w)); try typeclasses_eauto.
  - apply mkMetadata;
      Control.dispatch
        [ (fun _ => apply name)
          ; (fun _ => apply type_alias)
          ; (fun _ => apply variable_type)
          ; (fun _ => apply normalized_type)
          ; (fun _ => apply is_local)
          ; (fun _ => apply is_global)
          ; (fun _ => apply is_deterministic)
          ; (fun _ => apply is_non_deterministic)
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply x)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
          ; (fun _ => apply is_first_class_type)
          ; (fun _ => apply is_function_pointer)
        ];
      apply w.
  - apply is_indexable.
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
          ; (fun _ => apply normalized_type)
          ; (fun _ => apply is_local)
          ; (fun _ => apply is_global)
          ; (fun _ => apply is_deterministic)
          ; (fun _ => apply is_non_deterministic)
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_indexable)
          ; (fun _ => apply x)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
          ; (fun _ => apply is_first_class_type)
          ; (fun _ => apply is_function_pointer)
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
          ; (fun _ => apply normalized_type)
          ; (fun _ => apply is_local)
          ; (fun _ => apply is_global)
          ; (fun _ => apply is_deterministic)
          ; (fun _ => apply is_non_deterministic)
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_indexable)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply x)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
          ; (fun _ => apply is_first_class_type)
          ; (fun _ => apply is_function_pointer)
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
          ; (fun _ => apply normalized_type)
          ; (fun _ => apply is_local)
          ; (fun _ => apply is_global)
          ; (fun _ => apply is_deterministic)
          ; (fun _ => apply is_non_deterministic)
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_indexable)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply x)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
          ; (fun _ => apply is_first_class_type)
          ; (fun _ => apply is_function_pointer)
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
          ; (fun _ => apply normalized_type)
          ; (fun _ => apply is_local)
          ; (fun _ => apply is_global)
          ; (fun _ => apply is_deterministic)
          ; (fun _ => apply is_non_deterministic)
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_indexable)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply x)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
          ; (fun _ => apply is_first_class_type)
          ; (fun _ => apply is_function_pointer)
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
          ; (fun _ => apply normalized_type)
          ; (fun _ => apply is_local)
          ; (fun _ => apply is_global)
          ; (fun _ => apply is_deterministic)
          ; (fun _ => apply is_non_deterministic)
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_indexable)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply x)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
          ; (fun _ => apply is_first_class_type)
          ; (fun _ => apply is_function_pointer)
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
          ; (fun _ => apply normalized_type)
          ; (fun _ => apply is_local)
          ; (fun _ => apply is_global)
          ; (fun _ => apply is_deterministic)
          ; (fun _ => apply is_non_deterministic)
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_indexable)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply x)
          ; (fun _ => apply is_sized_type_alias)
          ; (fun _ => apply is_first_class_type)
          ; (fun _ => apply is_function_pointer)
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
          ; (fun _ => apply normalized_type)
          ; (fun _ => apply is_local)
          ; (fun _ => apply is_global)
          ; (fun _ => apply is_deterministic)
          ; (fun _ => apply is_non_deterministic)
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_indexable)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply x)
          ; (fun _ => apply is_first_class_type)
          ; (fun _ => apply is_function_pointer)
        ];
      apply w.
  - apply is_sized_type_alias.
Defined.

Definition is_first_class_type' {s : StorageType} : Lens' (Metadata s) (Component s Field unit).
  red.
  intros f F afa w.
  refine open_constr:((fun x => _) <$> afa (_ w)); try typeclasses_eauto.
  - apply mkMetadata;
      Control.dispatch
        [ (fun _ => apply name)
          ; (fun _ => apply type_alias)
          ; (fun _ => apply variable_type)
          ; (fun _ => apply normalized_type)
          ; (fun _ => apply is_local)
          ; (fun _ => apply is_global)
          ; (fun _ => apply is_deterministic)
          ; (fun _ => apply is_non_deterministic)
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_indexable)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
          ; (fun _ => apply x)
          ; (fun _ => apply is_function_pointer)
        ];
      apply w.
  - apply is_first_class_type.
Defined.

Definition is_function_pointer' {s : StorageType} : Lens' (Metadata s) (Component s Field unit).
  red.
  intros f F afa w.
  refine open_constr:((fun x => _) <$> afa (_ w)); try typeclasses_eauto.
  - apply mkMetadata;
      Control.dispatch
        [ (fun _ => apply name)
          ; (fun _ => apply type_alias)
          ; (fun _ => apply variable_type)
          ; (fun _ => apply normalized_type)
          ; (fun _ => apply is_local)
          ; (fun _ => apply is_global)
          ; (fun _ => apply is_deterministic)
          ; (fun _ => apply is_non_deterministic)
          ; (fun _ => apply from_pointer)
          ; (fun _ => apply is_pointer)
          ; (fun _ => apply is_sized_pointer)
          ; (fun _ => apply is_sized)
          ; (fun _ => apply is_aggregate)
          ; (fun _ => apply is_indexable)
          ; (fun _ => apply is_vector)
          ; (fun _ => apply is_array)
          ; (fun _ => apply is_struct)
          ; (fun _ => apply is_non_void)
          ; (fun _ => apply is_ptr_vector)
          ; (fun _ => apply is_sized_ptr_vector)
          ; (fun _ => apply is_sized_type_alias)
          ; (fun _ => apply is_first_class_type)
          ; (fun _ => apply x)
        ];
      apply w.
  - apply is_function_pointer.
Defined.

Definition ident_to_raw_id (i : ident) :=
  match i with
  | ID_Global id => id
  | ID_Local id => id
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

Definition names'' {m} : Traversal (Metadata (WorldOf m)) (Metadata (WorldOf m)) (Component (WorldOf m) Field ident) (Component (WorldOf m) Field ident).
  red.
  intros f F focus meta.
  refine open_constr:(pure (mkMetadata (WorldOf m)) <*> _ <*> _ <*> _ <*> _ <*> _ <*> _ <*> _
                        <*> _ <*> _ <*> _ <*> _ <*> _ <*> _ <*> _ <*> _ <*> _ <*> _ <*> _
                        <*> _ <*> _ <*> _ <*> _ <*> _);
    try typeclasses_eauto.
  - apply (focus (name _ meta)).
  - apply (pure (type_alias _ meta)).
  - apply (pure (variable_type _ meta)).
  - apply (pure (normalized_type _ meta)).
  - apply (pure (is_local _ meta)).
  - apply (pure (is_global _ meta)).
  - apply (pure (is_deterministic _ meta)).
  - apply (pure (is_non_deterministic _ meta)).
  - apply (pure (from_pointer _ meta)).
  - apply (pure (is_pointer _ meta)).
  - apply (pure (is_sized_pointer _ meta)).
  - apply (pure (is_sized _ meta)).
  - apply (pure (is_aggregate _ meta)).
  - apply (pure (is_indexable _ meta)).
  - apply (pure (is_vector _ meta)).
  - apply (pure (is_array _ meta)).
  - apply (pure (is_struct _ meta)).
  - apply (pure (is_non_void _ meta)).
  - apply (pure (is_ptr_vector _ meta)).
  - apply (pure (is_sized_ptr_vector _ meta)).
  - apply (pure (is_sized_type_alias _ meta)).
  - apply (pure (is_first_class_type _ meta)).
  - apply (pure (is_function_pointer _ meta)).
Defined.

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

Program Definition efind
  {w m a} `{Monad m} `{@MetadataStore m Metadata (SystemState w m)}
  {es E} `{ToEnt E} `{Foldable es E}
  (t : EntTarget w m (E:=E))
  (q : QueryT Metadata m a) : SystemT w m (option a)
  := es <- t;;
     _.
Next Obligation.
  refine
    open_constr:
      (fold _
         (fun (k : E) (acc : SystemT w m (option a)) =>
            let e := toEnt k in
            meta <- getEntity e;;
            qres <- lift (unQueryT q e meta);;
            match qres with
            | Some _ => ret qres
            | None => acc
            end
         ) (ret None) es);
    try typeclasses_eauto.
Defined.
