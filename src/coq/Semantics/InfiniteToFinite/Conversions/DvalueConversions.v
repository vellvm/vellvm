From Coq Require Import
     Relations
     String
     List
     Lia
     ZArith
     Morphisms.

Require Import Coq.Logic.ProofIrrelevance.

From Vellvm Require Import
     Semantics.InterpretationStack
     Semantics.LLVMEvents
     Semantics.Denotation
     Semantics.MemoryAddress
     Semantics.Memory.Sizeof
     Semantics.Lang
     Semantics.InterpretationStack
     Semantics.TopLevel
     Semantics.DynamicValues
     Semantics.LLVMParams
     Semantics.InfiniteToFinite.Conversions.BaseConversions
     Semantics.InfiniteToFinite.R2Injective
     Syntax.DynamicTypes
     Theory.TopLevelRefinements
     Theory.ContainsUB
     Utils.Error
     Utils.Monads
     Utils.MapMonadExtra
     Utils.PropT
     Utils.InterpProp
     Utils.ListUtil
     Utils.Tactics
     Utils.OOMRutt
     Utils.OOMRuttProps
     Handlers.MemoryModules.FiniteAddresses
     Handlers.MemoryModules.InfiniteAddresses
     Handlers.MemoryModelImplementation.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor.

From ITree Require Import
     ITree
     Basics
     Basics.HeterogeneousRelations
     Eq.Rutt
     Eq.RuttFacts
     Eq.Eqit
     Eq.EqAxiom.

Require Import Coq.Program.Equality.
Require Import Paco.paco.

Import InterpFacts.

Import MonadNotation.
Import ListNotations.


Module Type DVConvert (LP1 : LLVMParams) (LP2 : LLVMParams) (AC : AddrConvert LP1.ADDR LP2.ADDR) (Events1 : LLVM_INTERACTIONS LP1.ADDR LP1.IP LP1.SIZEOF) (Events2 : LLVM_INTERACTIONS LP2.ADDR LP2.IP LP2.SIZEOF).
  Import AC.

  Module DV1 := Events1.DV.
  Module DV2 := Events2.DV.

(* TODO: Move into Dvalue *)
  Ltac solve_dvalue_measure :=
    match goal with
    | Hin : In ?e ?fields |- context [DV1.dvalue_measure _]
      => pose proof list_sum_map DV1.dvalue_measure _ _ Hin;
        cbn; lia
    | Hin : InT ?e ?fields |- context [DV1.dvalue_measure _]
      => pose proof list_sum_map_InT DV1.dvalue_measure _ _ Hin;
        cbn; lia
    | H: Some ?f = List.nth_error ?fields _ |- context [DV1.dvalue_measure ?f]
      => symmetry in H; apply nth_error_In in H;
        pose proof list_sum_map DV1.dvalue_measure _ _ H;
        cbn; lia
    end.

  Ltac solve_uvalue_measure :=
    cbn;
    first [ lia
          | match goal with
            | _ : _ |- context [(DV1.uvalue_measure ?t + fold_right _ _ _)%nat]
              => pose proof (DV1.uvalue_measure_gt_0 t); unfold list_sum; lia
            end
          | match goal with
            | HIn : In ?x ?xs |- context [ list_sum (map ?f _)] =>
                pose proof (list_sum_map f x xs HIn)
            end;
            cbn in *; lia
          | match goal with
            | HIn : InT ?x ?xs |- context [ list_sum (map ?f _)] =>
                pose proof (list_sum_map_InT f x xs HIn)
            end;
            cbn in *; lia
      ].

  
  (* Parameter dvalue_convert_lazy : DV1.dvalue -> DV2.dvalue. *)
  (* Parameter uvalue_convert_lazy : DV1.uvalue -> DV2.uvalue. *)
  (*
  Parameter dvalue_convert_lazy_equation :
    forall dv,
      dvalue_convert_lazy dv =
        match dv with
        | DV1.DVALUE_Addr a =>
            match addr_convert a with
            | Oom msg => DV2.DVALUE_Oom DTYPE_Pointer
            | NoOom a' => DV2.DVALUE_Addr a'
            end
        | DV1.DVALUE_I1 x  => DV2.DVALUE_I1 x
        | DV1.DVALUE_I8 x  => DV2.DVALUE_I8 x
        | DV1.DVALUE_I32 x => DV2.DVALUE_I32 x
        | DV1.DVALUE_I64 x => DV2.DVALUE_I64 x
        | DV1.DVALUE_IPTR x =>
            let xz := LP1.IP.to_Z x in
            match LP2.IP.from_Z xz with
            | Oom msg => DV2.DVALUE_Oom DTYPE_IPTR
            | NoOom x' => DV2.DVALUE_IPTR x'
            end
        | DV1.DVALUE_Double x => DV2.DVALUE_Double x
        | DV1.DVALUE_Float x => DV2.DVALUE_Float x
        | DV1.DVALUE_Poison t => DV2.DVALUE_Poison t
        | DV1.DVALUE_Oom t => DV2.DVALUE_Oom t
        | DV1.DVALUE_None => DV2.DVALUE_None
        | DV1.DVALUE_Struct fields =>
            let fields' := map_In fields (fun elt HIn => dvalue_convert_lazy elt)in
            DV2.DVALUE_Struct fields'
        | DV1.DVALUE_Packed_struct fields =>
            let fields' := map_In fields (fun elt HIn => dvalue_convert_lazy elt)in
            DV2.DVALUE_Packed_struct fields'
        | DV1.DVALUE_Array elts =>
            let elts' := map_In elts (fun elt HIn => dvalue_convert_lazy elt)in
            DV2.DVALUE_Array elts'
        | DV1.DVALUE_Vector elts =>
            let elts' := map_In elts (fun elt HIn => dvalue_convert_lazy elt)in
            DV2.DVALUE_Vector elts'
        end.

  Parameter uvalue_convert_lazy_equation:
    forall uv,
      uvalue_convert_lazy uv =
        match uv with
        | DV1.UVALUE_Addr a =>
            match addr_convert a with
            | Oom msg => DV2.UVALUE_Oom DTYPE_Pointer
            | NoOom a' => DV2.UVALUE_Addr a'
            end
        | DV1.UVALUE_I1 x  => DV2.UVALUE_I1 x
        | DV1.UVALUE_I8 x  => DV2.UVALUE_I8 x
        | DV1.UVALUE_I32 x => DV2.UVALUE_I32 x
        | DV1.UVALUE_I64 x => DV2.UVALUE_I64 x
        | DV1.UVALUE_IPTR x =>
            let xz := LP1.IP.to_Z x in
            match LP2.IP.from_Z xz with
            | Oom msg => DV2.UVALUE_Oom DTYPE_IPTR
            | NoOom x' => DV2.UVALUE_IPTR x'
            end
        | DV1.UVALUE_Double x => DV2.UVALUE_Double x
        | DV1.UVALUE_Float x => DV2.UVALUE_Float x
        | DV1.UVALUE_Poison t => DV2.UVALUE_Poison t
        | DV1.UVALUE_Oom t => DV2.UVALUE_Oom t
        | DV1.UVALUE_None => DV2.UVALUE_None
        | DV1.UVALUE_Struct fields =>
            let fields' := map_In fields (fun elt HIn => uvalue_convert_lazy elt)in
            DV2.UVALUE_Struct fields'
        | DV1.UVALUE_Packed_struct fields =>
            let fields' := map_In fields (fun elt HIn => uvalue_convert_lazy elt)in
            DV2.UVALUE_Packed_struct fields'
        | DV1.UVALUE_Array elts =>
            let elts' := map_In elts (fun elt HIn => uvalue_convert_lazy elt)in
            DV2.UVALUE_Array elts'
        | DV1.UVALUE_Vector elts =>
            let elts' := map_In elts (fun elt HIn => uvalue_convert_lazy elt)in
            DV2.UVALUE_Vector elts'
        | DV1.UVALUE_Undef dt =>
            (* Could be a bit odd with intptr *)
            DV2.UVALUE_Undef dt
        | DV1.UVALUE_IBinop iop v1 v2 =>
            let v1' := uvalue_convert_lazy v1 in
            let v2' := uvalue_convert_lazy v2 in
            DV2.UVALUE_IBinop iop v1' v2'
        | DV1.UVALUE_ICmp cmp v1 v2 =>
            let v1' := uvalue_convert_lazy v1 in
            let v2' := uvalue_convert_lazy v2 in
            DV2.UVALUE_ICmp cmp v1' v2'
        | DV1.UVALUE_FBinop fop fm v1 v2 =>
            let v1' := uvalue_convert_lazy v1 in
            let v2' := uvalue_convert_lazy v2 in
            DV2.UVALUE_FBinop fop fm v1' v2'
        | DV1.UVALUE_FCmp cmp v1 v2 =>
            let v1' := uvalue_convert_lazy v1 in
            let v2' := uvalue_convert_lazy v2 in
            DV2.UVALUE_FCmp cmp v1' v2'
        | DV1.UVALUE_Conversion conv t_from v t_to =>
            let v' := uvalue_convert_lazy v in
            DV2.UVALUE_Conversion conv t_from v' t_to
        | DV1.UVALUE_GetElementPtr t ptrval idxs =>
            let ptrval' := uvalue_convert_lazy ptrval in
            let idxs' := map_In idxs (fun elt Hin => uvalue_convert_lazy elt) in
            DV2.UVALUE_GetElementPtr t ptrval' idxs'
        | DV1.UVALUE_ExtractElement t vec idx =>
            let vec' := uvalue_convert_lazy vec in
            let idx' := uvalue_convert_lazy idx in
            DV2.UVALUE_ExtractElement t vec' idx'
        | DV1.UVALUE_InsertElement t vec elt idx =>
            let vec' := uvalue_convert_lazy vec in
            let elt' := uvalue_convert_lazy elt in
            let idx' := uvalue_convert_lazy idx in
            DV2.UVALUE_InsertElement t vec' elt' idx'
        | DV1.UVALUE_ShuffleVector vec1 vec2 idxmask =>
            let vec1' := uvalue_convert_lazy vec1 in
            let vec2' := uvalue_convert_lazy vec2 in
            let idxmask' := uvalue_convert_lazy idxmask in
            DV2.UVALUE_ShuffleVector vec1' vec2' idxmask'
        | DV1.UVALUE_ExtractValue t vec idxs =>
            let vec' := uvalue_convert_lazy vec in
            DV2.UVALUE_ExtractValue t vec' idxs
        | DV1.UVALUE_InsertValue t vec elt idxs =>
            let vec' := uvalue_convert_lazy vec in
            let elt' := uvalue_convert_lazy elt in
            DV2.UVALUE_InsertValue t vec' elt' idxs
        | DV1.UVALUE_Select cnd v1 v2 =>
            let cnd' := uvalue_convert_lazy cnd in
            let v1' := uvalue_convert_lazy v1 in
            let v2' := uvalue_convert_lazy v2 in
            DV2.UVALUE_Select cnd' v1' v2'
        | DV1.UVALUE_ExtractByte uv dt idx sid =>
            let uv' := uvalue_convert_lazy uv in
            let idx' := uvalue_convert_lazy idx in
            DV2.UVALUE_ExtractByte uv' dt idx' sid
        | DV1.UVALUE_ConcatBytes uvs dt =>
            let uvs' := map_In uvs (fun elt Hin => uvalue_convert_lazy elt) in
            DV2.UVALUE_ConcatBytes uvs' dt
        end.

  Definition uvalue_converted_lazy (uv1 : DV1.uvalue) (uv2 : DV2.uvalue) : Prop :=
    uvalue_convert_lazy uv1 = uv2.

  Definition dvalue_converted_lazy (dv1 : DV1.dvalue) (dv2 : DV2.dvalue) : Prop :=
    dvalue_convert_lazy dv1 = dv2.

  Parameter dvalue_refine_lazy : DV1.dvalue -> DV2.dvalue -> Prop.

  Parameter dvalue_refine_lazy_equation :
    forall dv1 dv2,
      dvalue_refine_lazy dv1 dv2 =
        (dvalue_converted_lazy dv1 dv2 \/
         match dv2 with
         | DV2.DVALUE_Oom t2 => DV1.dvalue_has_dtyp dv1 t2
         | DV2.DVALUE_Struct fields2 =>
             match dv1 with
             | DV1.DVALUE_Struct fields1 => Forall2_HIn fields1 fields2 (fun e1 e2 IN1 IN2 => dvalue_refine_lazy e1 e2)
             | _ => False
             end
         | DV2.DVALUE_Packed_struct fields2 =>
             match dv1 with
             | DV1.DVALUE_Packed_struct fields1 =>
                 Forall2_HIn fields1 fields2 (fun e1 e2 IN1 IN2 => dvalue_refine_lazy e1 e2)
             | _ => False
             end
         | DV2.DVALUE_Array elts2 =>
             match dv1 with 
             | DV1.DVALUE_Array elts1 =>
                 Forall2_HIn elts1 elts2 (fun e1 e2 IN1 IN2 => dvalue_refine_lazy e1 e2)
             | _ => False
             end
         | DV2.DVALUE_Vector elts2 =>
             match dv1 with 
             | DV1.DVALUE_Vector elts1 =>
                 Forall2_HIn elts1 elts2 (fun e1 e2 IN1 IN2 => dvalue_refine_lazy e1 e2)
             | _ => False
             end
         | _ => False
         end).


  Parameter uvalue_refine_lazy : DV1.uvalue -> DV2.uvalue -> Prop.
  Parameter uvalue_refine_lazy_equation :
    forall uv1 uv2,
      uvalue_refine_lazy uv1 uv2 =
        (uvalue_converted_lazy uv1 uv2 \/
           match uv2 with
           | DV2.UVALUE_Oom t2 => DV1.uvalue_has_dtyp uv1 t2
           | DV2.UVALUE_Struct fields2 =>
               match uv1 with
               | DV1.UVALUE_Struct fields1 => Forall2_HIn fields1 fields2 (fun e1 e2 IN1 IN2 => uvalue_refine_lazy e1 e2)
               | _ => False
               end
           | DV2.UVALUE_Packed_struct fields2 =>
               match uv1 with
               | DV1.UVALUE_Packed_struct fields1 =>
                   Forall2_HIn fields1 fields2 (fun e1 e2 IN1 IN2 => uvalue_refine_lazy e1 e2)
               | _ => False
               end
           | DV2.UVALUE_Array elts2 =>
               match uv1 with
               | DV1.UVALUE_Array elts1 => 
                   Forall2_HIn elts1 elts2 (fun e1 e2 IN1 IN2 => uvalue_refine_lazy e1 e2)
               | _ => False
               end
           | DV2.UVALUE_Vector elts2 =>
               match uv1 with
               | DV1.UVALUE_Vector elts1 => 
                   Forall2_HIn elts1 elts2 (fun e1 e2 IN1 IN2 => uvalue_refine_lazy e1 e2)
               | _ => False
               end
           | DV2.UVALUE_IBinop iop2 v1_2 v2_2 =>
               match uv1 with
               | DV1.UVALUE_IBinop iop1 v1_1 v2_1 => 
                   iop1 = iop2 /\
                     uvalue_refine_lazy v1_1 v1_2 /\
                     uvalue_refine_lazy v2_1 v2_2
               | _ => False
               end
           | DV2.UVALUE_ICmp cmp2 v1_2 v2_2 =>
               match uv1 with
               | DV1.UVALUE_ICmp cmp1 v1_1 v2_1 => 
                   cmp1 = cmp2 /\
                     uvalue_refine_lazy v1_1 v1_2 /\
                     uvalue_refine_lazy v2_1 v2_2
               | _ => False
               end
           | DV2.UVALUE_FBinop fop2 fm2 v1_2 v2_2 =>
               match uv1 with
               | DV1.UVALUE_FBinop fop1 fm1 v1_1 v2_1 => 
                   fop1 = fop2 /\
                     fm1 = fm2 /\
                     uvalue_refine_lazy v1_1 v1_2 /\
                     uvalue_refine_lazy v2_1 v2_2
               | _ => False
               end
           | DV2.UVALUE_FCmp cmp2 v1_2 v2_2 =>
               match uv1 with
               | DV1.UVALUE_FCmp cmp1 v1_1 v2_1 => 
                   cmp1 = cmp2 /\
                     uvalue_refine_lazy v1_1 v1_2 /\
                     uvalue_refine_lazy v2_1 v2_2
               | _ => False
               end
           | DV2.UVALUE_Conversion conv2 t_from2 v2 t_to2 =>
               match uv1 with
               | DV1.UVALUE_Conversion conv1 t_from1 v1 t_to1 => 
                   conv1 = conv2 /\
                     uvalue_refine_lazy v1 v2 /\
                     t_from1 = t_from2 /\
                     t_to1 = t_to2
               | _ => False
               end
           | DV2.UVALUE_GetElementPtr t2 ptrval2 idxs2 =>
               match uv1 with
               | DV1.UVALUE_GetElementPtr t1 ptrval1 idxs1 => 
                   t1 = t2 /\
                     uvalue_refine_lazy ptrval1 ptrval2 /\
                     Forall2_HIn idxs1 idxs2 (fun ix1 ix2 IN1 IN2 => uvalue_refine_lazy ix1 ix2)
               | _ => False
               end
           | DV2.UVALUE_ExtractElement vec_typ2 vec2 idx2 =>
               match uv1 with
               | DV1.UVALUE_ExtractElement vec_typ1 vec1 idx1 => 
                   vec_typ1 = vec_typ2 /\
                     uvalue_refine_lazy vec1 vec2 /\
                     uvalue_refine_lazy idx1 idx2
               | _ => False
               end
           | DV2.UVALUE_InsertElement vec_typ2 vec2 elt2 idx2 =>
               match uv1 with
               | DV1.UVALUE_InsertElement vec_typ1 vec1 elt1 idx1 => 
                   vec_typ1 = vec_typ2 /\
                     uvalue_refine_lazy vec1 vec2 /\
                     uvalue_refine_lazy elt1 elt2 /\
                     uvalue_refine_lazy idx1 idx2
               | _ => False
               end
           | DV2.UVALUE_ShuffleVector vec1_2 vec2_2 idxmask2 =>
               match uv1 with
               | DV1.UVALUE_ShuffleVector vec1_1 vec2_1 idxmask1 =>
                   uvalue_refine_lazy vec1_1 vec1_2 /\
                     uvalue_refine_lazy vec2_1 vec2_2 /\
                     uvalue_refine_lazy idxmask1 idxmask2
               | _ => False
               end
           | DV2.UVALUE_ExtractValue vec_typ2 vec2 idxs2 =>
               match uv1 with
               | DV1.UVALUE_ExtractValue vec_typ1 vec1 idxs1 => 
                   vec_typ1 = vec_typ2 /\
                     uvalue_refine_lazy vec1 vec2 /\
                     idxs1 = idxs2
               | _ => False
               end
           | DV2.UVALUE_InsertValue vec_typ2 vec2 elt2 idxs2 =>
               match uv1 with
               | DV1.UVALUE_InsertValue vec_typ1 vec1 elt1 idxs1 => 
                   vec_typ1 = vec_typ2 /\
                     uvalue_refine_lazy vec1 vec2 /\
                     uvalue_refine_lazy elt1 elt2 /\
                     idxs1 = idxs2
               | _ => False
               end
           | DV2.UVALUE_Select cnd2 v1_2 v2_2 =>
               match uv1 with
               | DV1.UVALUE_Select cnd1 v1_1 v2_1 => 
                   uvalue_refine_lazy cnd1 cnd2 /\
                     uvalue_refine_lazy v1_1 v1_2 /\
                     uvalue_refine_lazy v2_1 v2_2
               | _ => False
               end
           | DV2.UVALUE_ExtractByte uv2 dt2 idx2 sid2 =>
               match uv1 with
               | DV1.UVALUE_ExtractByte uv1 dt1 idx1 sid1 => 
                   uvalue_refine_lazy uv1 uv2 /\
                     dt1 = dt2 /\
                     uvalue_refine_lazy idx1 idx2 /\
                     sid1 = sid2
               | _ => False
               end
           | DV2.UVALUE_ConcatBytes uvs2 dt2 =>
               match uv1 with
               | DV1.UVALUE_ConcatBytes uvs1 dt1 => 
                   Forall2_HIn uvs1 uvs2 (fun uv1 uv2 IN1 IN2 => uvalue_refine_lazy uv1 uv2) /\
                     dt1 = dt2
               | _ => False
               end
           | _ => False
           end).

  Parameter dvalue_refine_lazy_dvalue_convert_lazy :
    forall dv,
      dvalue_refine_lazy dv (dvalue_convert_lazy dv).

  Parameter uvalue_refine_lazy_uvalue_convert_lazy :
    forall dv,
      uvalue_refine_lazy dv (uvalue_convert_lazy dv).

  Parameter dvalue_refine_lazy_dvalue_converted_lazy :
    forall dv1 dv2,
      dvalue_converted_lazy dv1 dv2 ->
      dvalue_refine_lazy dv1 dv2.

  Parameter uvalue_refine_uvalue_converted :
    forall uv1 uv2,
      uvalue_converted_lazy uv1 uv2 ->
      uvalue_refine_lazy uv1 uv2.
   *)
  
  Parameter dvalue_convert_strict : DV1.dvalue -> OOM DV2.dvalue.
  Parameter dvalue_convert_strict_equation :
    forall dv,
      dvalue_convert_strict dv =
        match dv with
        | DV1.DVALUE_Addr a =>
            a' <- addr_convert a;;
            ret (DV2.DVALUE_Addr a')
        | DV1.DVALUE_I1 x  => ret (DV2.DVALUE_I1 x)
        | DV1.DVALUE_I8 x  => ret (DV2.DVALUE_I8 x)
        | DV1.DVALUE_I32 x => ret (DV2.DVALUE_I32 x)
        | DV1.DVALUE_I64 x => ret (DV2.DVALUE_I64 x)
        | DV1.DVALUE_IPTR x =>
            let xz := LP1.IP.to_Z x in
            x' <- LP2.IP.from_Z xz;;
            ret (DV2.DVALUE_IPTR x')
        | DV1.DVALUE_Double x => ret (DV2.DVALUE_Double x)
        | DV1.DVALUE_Float x => ret (DV2.DVALUE_Float x)
        | DV1.DVALUE_Oom t => ret (DV2.DVALUE_Oom t)
        | DV1.DVALUE_Poison t => ret (DV2.DVALUE_Poison t)
        | DV1.DVALUE_None => ret DV2.DVALUE_None
        | DV1.DVALUE_Struct fields =>
            fields' <- map_monad_InT fields (fun elt Hin => dvalue_convert_strict elt);;
            ret (DV2.DVALUE_Struct fields')
        | DV1.DVALUE_Packed_struct fields =>
            fields' <- map_monad_InT fields (fun elt Hin => dvalue_convert_strict elt);;
            ret (DV2.DVALUE_Packed_struct fields')
        | DV1.DVALUE_Array elts =>
            elts' <- map_monad_InT elts (fun elt Hin => dvalue_convert_strict elt);;
            ret (DV2.DVALUE_Array elts')
        | DV1.DVALUE_Vector elts =>
            elts' <- map_monad_InT elts (fun elt Hin => dvalue_convert_strict elt);;
            ret (DV2.DVALUE_Vector elts')
        end.
  
  Parameter uvalue_convert_strict : DV1.uvalue -> OOM DV2.uvalue.
  Parameter uvalue_convert_strict_equation:
    forall uv,
      uvalue_convert_strict uv =
        match uv with
        | DV1.UVALUE_Addr a =>
            a' <- addr_convert a;;
            ret (DV2.UVALUE_Addr a')
        | DV1.UVALUE_I1 x  => ret (DV2.UVALUE_I1 x)
        | DV1.UVALUE_I8 x  => ret (DV2.UVALUE_I8 x)
        | DV1.UVALUE_I32 x => ret (DV2.UVALUE_I32 x)
        | DV1.UVALUE_I64 x => ret (DV2.UVALUE_I64 x)
        | DV1.UVALUE_IPTR x =>
            let xz := LP1.IP.to_Z x in
            x' <- LP2.IP.from_Z xz;;
            ret (DV2.UVALUE_IPTR x')
        | DV1.UVALUE_Double x => ret (DV2.UVALUE_Double x)
        | DV1.UVALUE_Float x => ret (DV2.UVALUE_Float x)
        | DV1.UVALUE_Oom t => ret (DV2.UVALUE_Oom t)
        | DV1.UVALUE_Poison t => ret (DV2.UVALUE_Poison t)
        | DV1.UVALUE_None => ret DV2.UVALUE_None
        | DV1.UVALUE_Struct fields =>
            fields' <- map_monad_InT fields (fun elt Hin => uvalue_convert_strict elt);;
            ret (DV2.UVALUE_Struct fields')
        | DV1.UVALUE_Packed_struct fields =>
            fields' <- map_monad_InT fields (fun elt Hin => uvalue_convert_strict elt);;
            ret (DV2.UVALUE_Packed_struct fields')
        | DV1.UVALUE_Array elts =>
            elts' <- map_monad_InT elts (fun elt Hin => uvalue_convert_strict elt);;
            ret (DV2.UVALUE_Array elts')
        | DV1.UVALUE_Vector elts =>
            elts' <- map_monad_InT elts (fun elt Hin => uvalue_convert_strict elt);;
            ret (DV2.UVALUE_Vector elts')
        | DV1.UVALUE_Undef dt =>
            (* Could be a bit odd with intptr *)
            ret (DV2.UVALUE_Undef dt)
        | DV1.UVALUE_IBinop iop v1 v2 =>
            v1' <- uvalue_convert_strict v1;;
            v2' <- uvalue_convert_strict v2;;
            ret (DV2.UVALUE_IBinop iop v1' v2')
        | DV1.UVALUE_ICmp cmp v1 v2 =>
            v1' <- uvalue_convert_strict v1;;
            v2' <- uvalue_convert_strict v2;;
            ret (DV2.UVALUE_ICmp cmp v1' v2')
        | DV1.UVALUE_FBinop fop fm v1 v2 =>
            v1' <- uvalue_convert_strict v1;;
            v2' <- uvalue_convert_strict v2;;
            ret (DV2.UVALUE_FBinop fop fm v1' v2')
        | DV1.UVALUE_FCmp cmp v1 v2 =>
            v1' <- uvalue_convert_strict v1;;
            v2' <- uvalue_convert_strict v2;;
            ret (DV2.UVALUE_FCmp cmp v1' v2')
        | DV1.UVALUE_Conversion conv t_from v t_to =>
            v' <- uvalue_convert_strict v;;
            ret (DV2.UVALUE_Conversion conv t_from v' t_to)
        | DV1.UVALUE_GetElementPtr t ptrval idxs =>
            ptrval' <- uvalue_convert_strict ptrval;;
            idxs' <- map_monad_InT idxs (fun elt Hin => uvalue_convert_strict elt);;
            ret (DV2.UVALUE_GetElementPtr t ptrval' idxs')
        | DV1.UVALUE_ExtractElement t vec idx =>
            vec' <- uvalue_convert_strict vec;;
            idx' <- uvalue_convert_strict idx;;
            ret (DV2.UVALUE_ExtractElement t vec' idx')
        | DV1.UVALUE_InsertElement t vec elt idx =>
            vec' <- uvalue_convert_strict vec;;
            elt' <- uvalue_convert_strict elt;;
            idx' <- uvalue_convert_strict idx;;
            ret (DV2.UVALUE_InsertElement t vec' elt' idx')
        | DV1.UVALUE_ShuffleVector vec1 vec2 idxmask =>
            vec1' <- uvalue_convert_strict vec1;;
            vec2' <- uvalue_convert_strict vec2;;
            idxmask' <- uvalue_convert_strict idxmask;;
            ret (DV2.UVALUE_ShuffleVector vec1' vec2' idxmask')
        | DV1.UVALUE_ExtractValue t vec idxs =>
            vec' <- uvalue_convert_strict vec;;
            ret (DV2.UVALUE_ExtractValue t vec' idxs)
        | DV1.UVALUE_InsertValue t vec elt idxs =>
            vec' <- uvalue_convert_strict vec;;
            elt' <- uvalue_convert_strict elt;;
            ret (DV2.UVALUE_InsertValue t vec' elt' idxs)
        | DV1.UVALUE_Select cnd v1 v2 =>
            cnd' <- uvalue_convert_strict cnd;;
            v1' <- uvalue_convert_strict v1;;
            v2' <- uvalue_convert_strict v2;;
            ret (DV2.UVALUE_Select cnd' v1' v2')
        | DV1.UVALUE_ExtractByte uv dt idx sid =>
            uv' <- uvalue_convert_strict uv;;
            idx' <- uvalue_convert_strict idx;;
            ret (DV2.UVALUE_ExtractByte uv' dt idx' sid)
        | DV1.UVALUE_ConcatBytes uvs dt =>
            uvs' <- map_monad_InT uvs (fun elt Hin => uvalue_convert_strict elt);;
            ret (DV2.UVALUE_ConcatBytes uvs' dt)
        end.

  Definition dvalue_refine_strict (dv1 : DV1.dvalue) (dv2 : DV2.dvalue) : Prop
    := dvalue_convert_strict dv1 = NoOom dv2.

  Definition uvalue_refine_strict (uv1 : DV1.uvalue) (uv2 : DV2.uvalue) : Prop
    := uvalue_convert_strict uv1 = NoOom uv2.

  Parameter dvalue_refine_strict_equation :
    forall (dv1 : DV1.dvalue) (dv2 : DV2.dvalue),
      dvalue_refine_strict dv1 dv2 = (dvalue_convert_strict dv1 = NoOom dv2).

  Parameter uvalue_refine_strict_equation :
    forall (uv1 : DV1.uvalue) (uv2 : DV2.uvalue),
      uvalue_refine_strict uv1 uv2 = (uvalue_convert_strict uv1 = NoOom uv2).


  (*
  Parameter uvalue_convert_lazy_dv_to_uv_dvalue_convert_lazy :
    forall dv,
      uvalue_convert_lazy (DV1.dvalue_to_uvalue dv) = DV2.dvalue_to_uvalue (dvalue_convert_lazy dv).

  Parameter dvalue_refine_lazy_dvalue_to_uvalue :
    forall dv1 dv2,
      dvalue_refine_lazy dv1 dv2 ->
      uvalue_refine_lazy (DV1.dvalue_to_uvalue dv1) (DV2.dvalue_to_uvalue dv2).
   *)
  
  (* TODO: This seems better than lazy proof... Can probably do the same? *)
  Parameter dvalue_refine_strict_dvalue_to_uvalue :
    forall dv1 dv2,
      dvalue_refine_strict dv1 dv2 ->
      uvalue_refine_strict (DV1.dvalue_to_uvalue dv1) (DV2.dvalue_to_uvalue dv2).

  Hint Resolve dvalue_refine_strict_dvalue_to_uvalue : DVALUE_REFINE.

  (* TODO: Move this? *)
  Ltac unfold_dvalue_refine_strict :=
    rewrite dvalue_refine_strict_equation, dvalue_convert_strict_equation in *.

  Ltac unfold_dvalue_refine_strict_goal :=
    rewrite dvalue_refine_strict_equation, dvalue_convert_strict_equation.

  Ltac unfold_dvalue_refine_strict_in H :=
    rewrite dvalue_refine_strict_equation, dvalue_convert_strict_equation in H.

  Ltac unfold_uvalue_refine_strict :=
    rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation in *.

  Ltac unfold_uvalue_refine_strict_goal :=
    rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.

  Ltac unfold_uvalue_refine_strict_in H :=
    rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation in H.

  Ltac solve_uvalue_refine_strict :=
    solve [unfold_uvalue_refine_strict;
           cbn;
           solve [ auto
                 | rewrite addr_convert_null;
                   reflexivity
             ]
      ].

  Ltac solve_dvalue_refine_strict :=
    solve [unfold_dvalue_refine_strict;
           cbn;
           solve [ auto
                 | rewrite addr_convert_null;
                   reflexivity
             ]
      ].

  (** Parameters about is_concrete *)

  (*
  Parameter uvalue_convert_lazy_preserves_is_concrete :
    forall uv uvc b,
      uvalue_convert_lazy uv = uvc ->
      DV1.is_concrete uv = b ->
      DV2.is_concrete uvc = b.
   *)

  Parameter uvalue_refine_strict_preserves_is_concrete :
    forall uv uvc b,
      uvalue_refine_strict uv uvc ->
      DV1.is_concrete uv = b ->
      DV2.is_concrete uvc = b.

  (** Lemmas about uvalue_to_dvalue *)

  Parameter uvalue_to_dvalue_dvalue_refine_strict :
    forall uv1 uv2 dv1,
      uvalue_refine_strict uv1 uv2 ->
      DV1.uvalue_to_dvalue uv1 = inr dv1 ->
      exists dv2, DV2.uvalue_to_dvalue uv2 = inr dv2 /\
               dvalue_refine_strict dv1 dv2.

  Parameter uvalue_to_dvalue_dvalue_refine_strict_error :
    forall uv1 uv2 s,
      uvalue_refine_strict uv1 uv2 ->
      DV1.uvalue_to_dvalue uv1 = inl s ->
      exists s', DV2.uvalue_to_dvalue uv2 = inl s'.

  (** Lemmas about default dvalues *)

  (* TODO: Does this one belong here? *)
  Parameter default_dvalue_of_dtyp_i_dv1_dv2_same_error :
    forall sz s,
      DV1.default_dvalue_of_dtyp_i sz = inl s <->
        DV2.default_dvalue_of_dtyp_i sz = inl s.

  Parameter default_dvalue_of_dtyp_i_dv1_dv2_equiv :
    forall sz v1,
      DV1.default_dvalue_of_dtyp_i sz = inr v1 ->
      exists v2,
        DV2.default_dvalue_of_dtyp_i sz = inr v2 /\ dvalue_refine_strict v1 v2.

  Parameter default_dvalue_of_dtyp_i_dv1_dv2_equiv' :
    forall sz v2,
      DV2.default_dvalue_of_dtyp_i sz = inr v2 ->
      exists v1,
        DV1.default_dvalue_of_dtyp_i sz = inr v1 /\ dvalue_refine_strict v1 v2.

  Parameter default_dvalue_of_dtyp_dv1_dv2_equiv :
    forall dt v1,
      DV1.default_dvalue_of_dtyp dt = inr v1 ->
      exists v2, DV2.default_dvalue_of_dtyp dt = inr v2 /\ dvalue_refine_strict v1 v2.

  Parameter default_dvalue_of_dtyp_dv1_dv2_equiv' :
    forall dt v2,
      DV2.default_dvalue_of_dtyp dt = inr v2 ->
      exists v1, DV1.default_dvalue_of_dtyp dt = inr v1 /\ dvalue_refine_strict v1 v2.

  (* TODO: Move this? Seems more general... *)
  Parameter default_dvalue_of_dtyp_dv1_dv2_same_error :
    forall dt s,
      DV1.default_dvalue_of_dtyp dt = inl s <->
        DV2.default_dvalue_of_dtyp dt = inl s.

  (*
  Parameter dvalue_converted_lazy_R2_deterministic :
    R2_deterministic dvalue_converted_lazy.
   *)

  Parameter dvalue_refine_strict_R2_injective :
    R2_injective dvalue_refine_strict.

  (** Lemmas about values with types... *)

  (*
  Parameter dvalue_refine_lazy_oom :
    forall dv dt,
      DV1.dvalue_has_dtyp dv dt ->
      dvalue_refine_lazy dv (DV2.DVALUE_Oom dt).

  Parameter uvalue_refine_lazy_oom :
    forall uv dt,
      DV1.uvalue_has_dtyp uv dt ->
      uvalue_refine_lazy uv (DV2.UVALUE_Oom dt).
   *)
End DVConvert.

Module DVConvertMake (LP1 : LLVMParams) (LP2 : LLVMParams) (AC : AddrConvert LP1.ADDR LP2.ADDR) (Events1 : LLVM_INTERACTIONS LP1.ADDR LP1.IP LP1.SIZEOF) (Events2 : LLVM_INTERACTIONS LP2.ADDR LP2.IP LP2.SIZEOF) : DVConvert LP1 LP2 AC Events1 Events2
with Module DV1 := Events1.DV
with Module DV2 := Events2.DV.
  Import AC.
  Module DV1 := Events1.DV.
  Module DV2 := Events2.DV.  
  
  (* TODO: Move into Dvalue *)
  Ltac solve_dvalue_measure :=
    match goal with
    | Hin : In ?e ?fields |- context [DV1.dvalue_measure _]
      => pose proof list_sum_map DV1.dvalue_measure _ _ Hin;
        cbn; lia
    | Hin : InT ?e ?fields |- context [DV1.dvalue_measure _]
      => pose proof list_sum_map_InT DV1.dvalue_measure _ _ Hin;
        cbn; lia
    | H: Some ?f = List.nth_error ?fields _ |- context [DV1.dvalue_measure ?f]
      => symmetry in H; apply nth_error_In in H;
        pose proof list_sum_map DV1.dvalue_measure _ _ H;
        cbn; lia
    end.

  Ltac solve_uvalue_measure :=
    cbn;
    first [ lia
          | match goal with
            | _ : _ |- context [(DV1.uvalue_measure ?t + fold_right _ _ _)%nat]
              => pose proof (DV1.uvalue_measure_gt_0 t); unfold list_sum; lia
            end
          | match goal with
            | HIn : In ?x ?xs |- context [ list_sum (map ?f _)] =>
                pose proof (list_sum_map f x xs HIn)
            end;
            cbn in *; lia
          | match goal with
            | HIn : InT ?x ?xs |- context [ list_sum (map ?f _)] =>
                pose proof (list_sum_map_InT f x xs HIn)
            end;
            cbn in *; lia
      ].

  Obligation Tactic := try Tactics.program_simpl; try solve [cbn; try lia | solve_dvalue_measure | solve_uvalue_measure].

(*
  Program Fixpoint dvalue_convert_lazy (dv1 : DV1.dvalue) {measure (DV1.dvalue_measure dv1)} : DV2.dvalue
    := match dv1 with
       | DV1.DVALUE_Addr a =>
           match addr_convert a with
           | Oom msg => DV2.DVALUE_Oom DTYPE_Pointer
           | NoOom a' => DV2.DVALUE_Addr a'
           end
       | DV1.DVALUE_I1 x  => DV2.DVALUE_I1 x
       | DV1.DVALUE_I8 x  => DV2.DVALUE_I8 x
       | DV1.DVALUE_I32 x => DV2.DVALUE_I32 x
       | DV1.DVALUE_I64 x => DV2.DVALUE_I64 x
       | DV1.DVALUE_IPTR x =>
           let xz := LP1.IP.to_Z x in
           match LP2.IP.from_Z xz with
           | Oom msg => DV2.DVALUE_Oom DTYPE_IPTR
           | NoOom x' => DV2.DVALUE_IPTR x'
           end
       | DV1.DVALUE_Double x => DV2.DVALUE_Double x
       | DV1.DVALUE_Float x => DV2.DVALUE_Float x
       | DV1.DVALUE_Poison t => DV2.DVALUE_Poison t
       | DV1.DVALUE_Oom t => DV2.DVALUE_Oom t
       | DV1.DVALUE_None => DV2.DVALUE_None
       | DV1.DVALUE_Struct fields =>
           let fields' := map_In fields (fun elt HIn => dvalue_convert_lazy elt)in
           DV2.DVALUE_Struct fields'
       | DV1.DVALUE_Packed_struct fields =>
           let fields' := map_In fields (fun elt HIn => dvalue_convert_lazy elt)in
           DV2.DVALUE_Packed_struct fields'
       | DV1.DVALUE_Array elts =>
           let elts' := map_In elts (fun elt HIn => dvalue_convert_lazy elt)in
           DV2.DVALUE_Array elts'
       | DV1.DVALUE_Vector elts =>
           let elts' := map_In elts (fun elt HIn => dvalue_convert_lazy elt)in
           DV2.DVALUE_Vector elts'
       end.

    Program Fixpoint uvalue_convert_lazy (uv1 : DV1.uvalue) {measure (DV1.uvalue_measure uv1)} : DV2.uvalue
    := match uv1 with
       | DV1.UVALUE_Addr a =>
           match addr_convert a with
           | Oom msg => DV2.UVALUE_Oom DTYPE_Pointer
           | NoOom a' => DV2.UVALUE_Addr a'
           end
       | DV1.UVALUE_I1 x  => DV2.UVALUE_I1 x
       | DV1.UVALUE_I8 x  => DV2.UVALUE_I8 x
       | DV1.UVALUE_I32 x => DV2.UVALUE_I32 x
       | DV1.UVALUE_I64 x => DV2.UVALUE_I64 x
       | DV1.UVALUE_IPTR x =>
           let xz := LP1.IP.to_Z x in
           match LP2.IP.from_Z xz with
           | Oom msg => DV2.UVALUE_Oom DTYPE_IPTR
           | NoOom x' => DV2.UVALUE_IPTR x'
           end
       | DV1.UVALUE_Double x => DV2.UVALUE_Double x
       | DV1.UVALUE_Float x => DV2.UVALUE_Float x
       | DV1.UVALUE_Poison t => DV2.UVALUE_Poison t
       | DV1.UVALUE_Oom t => DV2.UVALUE_Oom t
       | DV1.UVALUE_None => DV2.UVALUE_None
       | DV1.UVALUE_Struct fields =>
           let fields' := map_In fields (fun elt HIn => uvalue_convert_lazy elt)in
           DV2.UVALUE_Struct fields'
       | DV1.UVALUE_Packed_struct fields =>
           let fields' := map_In fields (fun elt HIn => uvalue_convert_lazy elt)in
           DV2.UVALUE_Packed_struct fields'
       | DV1.UVALUE_Array elts =>
           let elts' := map_In elts (fun elt HIn => uvalue_convert_lazy elt)in
           DV2.UVALUE_Array elts'
       | DV1.UVALUE_Vector elts =>
           let elts' := map_In elts (fun elt HIn => uvalue_convert_lazy elt)in
           DV2.UVALUE_Vector elts'
       | DV1.UVALUE_Undef dt =>
           (* Could be a bit odd with intptr *)
           DV2.UVALUE_Undef dt
       | DV1.UVALUE_IBinop iop v1 v2 =>
           let v1' := uvalue_convert_lazy v1 in
           let v2' := uvalue_convert_lazy v2 in
           DV2.UVALUE_IBinop iop v1' v2'
       | DV1.UVALUE_ICmp cmp v1 v2 =>
           let v1' := uvalue_convert_lazy v1 in
           let v2' := uvalue_convert_lazy v2 in
           DV2.UVALUE_ICmp cmp v1' v2'
       | DV1.UVALUE_FBinop fop fm v1 v2 =>
           let v1' := uvalue_convert_lazy v1 in
           let v2' := uvalue_convert_lazy v2 in
           DV2.UVALUE_FBinop fop fm v1' v2'
       | DV1.UVALUE_FCmp cmp v1 v2 =>
           let v1' := uvalue_convert_lazy v1 in
           let v2' := uvalue_convert_lazy v2 in
           DV2.UVALUE_FCmp cmp v1' v2'
       | DV1.UVALUE_Conversion conv t_from v t_to =>
           let v' := uvalue_convert_lazy v in
           DV2.UVALUE_Conversion conv t_from v' t_to
       | DV1.UVALUE_GetElementPtr t ptrval idxs =>
           let ptrval' := uvalue_convert_lazy ptrval in
           let idxs' := map_In idxs (fun elt Hin => uvalue_convert_lazy elt) in
           DV2.UVALUE_GetElementPtr t ptrval' idxs'
       | DV1.UVALUE_ExtractElement t vec idx =>
           let vec' := uvalue_convert_lazy vec in
           let idx' := uvalue_convert_lazy idx in
           DV2.UVALUE_ExtractElement t vec' idx'
       | DV1.UVALUE_InsertElement t vec elt idx =>
           let vec' := uvalue_convert_lazy vec in
           let elt' := uvalue_convert_lazy elt in
           let idx' := uvalue_convert_lazy idx in
           DV2.UVALUE_InsertElement t vec' elt' idx'
       | DV1.UVALUE_ShuffleVector vec1 vec2 idxmask =>
           let vec1' := uvalue_convert_lazy vec1 in
           let vec2' := uvalue_convert_lazy vec2 in
           let idxmask' := uvalue_convert_lazy idxmask in
           DV2.UVALUE_ShuffleVector vec1' vec2' idxmask'
       | DV1.UVALUE_ExtractValue t vec idxs =>
           let vec' := uvalue_convert_lazy vec in
           DV2.UVALUE_ExtractValue t vec' idxs
       | DV1.UVALUE_InsertValue t vec elt idxs =>
           let vec' := uvalue_convert_lazy vec in
           let elt' := uvalue_convert_lazy elt in
           DV2.UVALUE_InsertValue t vec' elt' idxs
       | DV1.UVALUE_Select cnd v1 v2 =>
           let cnd' := uvalue_convert_lazy cnd in
           let v1' := uvalue_convert_lazy v1 in
           let v2' := uvalue_convert_lazy v2 in
           DV2.UVALUE_Select cnd' v1' v2'
       | DV1.UVALUE_ExtractByte uv dt idx sid =>
           let uv' := uvalue_convert_lazy uv in
           let idx' := uvalue_convert_lazy idx in
           DV2.UVALUE_ExtractByte uv' dt idx' sid
       | DV1.UVALUE_ConcatBytes uvs dt =>
           let uvs' := map_In uvs (fun elt Hin => uvalue_convert_lazy elt) in
           DV2.UVALUE_ConcatBytes uvs' dt
       end.

  Lemma dvalue_convert_lazy_equation :
    forall dv,
      dvalue_convert_lazy dv =
        match dv with
        | DV1.DVALUE_Addr a =>
            match addr_convert a with
            | Oom msg => DV2.DVALUE_Oom DTYPE_Pointer
            | NoOom a' => DV2.DVALUE_Addr a'
            end
        | DV1.DVALUE_I1 x  => DV2.DVALUE_I1 x
        | DV1.DVALUE_I8 x  => DV2.DVALUE_I8 x
        | DV1.DVALUE_I32 x => DV2.DVALUE_I32 x
        | DV1.DVALUE_I64 x => DV2.DVALUE_I64 x
        | DV1.DVALUE_IPTR x =>
            let xz := LP1.IP.to_Z x in
            match LP2.IP.from_Z xz with
            | Oom msg => DV2.DVALUE_Oom DTYPE_IPTR
            | NoOom x' => DV2.DVALUE_IPTR x'
            end
        | DV1.DVALUE_Double x => DV2.DVALUE_Double x
        | DV1.DVALUE_Float x => DV2.DVALUE_Float x
        | DV1.DVALUE_Poison t => DV2.DVALUE_Poison t
        | DV1.DVALUE_Oom t => DV2.DVALUE_Oom t
        | DV1.DVALUE_None => DV2.DVALUE_None
        | DV1.DVALUE_Struct fields =>
            let fields' := map_In fields (fun elt HIn => dvalue_convert_lazy elt)in
            DV2.DVALUE_Struct fields'
        | DV1.DVALUE_Packed_struct fields =>
            let fields' := map_In fields (fun elt HIn => dvalue_convert_lazy elt)in
            DV2.DVALUE_Packed_struct fields'
        | DV1.DVALUE_Array elts =>
            let elts' := map_In elts (fun elt HIn => dvalue_convert_lazy elt)in
            DV2.DVALUE_Array elts'
        | DV1.DVALUE_Vector elts =>
            let elts' := map_In elts (fun elt HIn => dvalue_convert_lazy elt)in
            DV2.DVALUE_Vector elts'
        end.
  Proof.
    intros dv.
    Transparent dvalue_convert_lazy.
    unfold dvalue_convert_lazy at 1.
    rewrite Wf.WfExtensionality.fix_sub_eq_ext at 1.
    destruct dv; try reflexivity.
    break_match; reflexivity.
    break_match; reflexivity.
  Qed.

  Lemma uvalue_convert_lazy_equation:
    forall uv,
      uvalue_convert_lazy uv =
        match uv with
        | DV1.UVALUE_Addr a =>
            match addr_convert a with
            | Oom msg => DV2.UVALUE_Oom DTYPE_Pointer
            | NoOom a' => DV2.UVALUE_Addr a'
            end
        | DV1.UVALUE_I1 x  => DV2.UVALUE_I1 x
        | DV1.UVALUE_I8 x  => DV2.UVALUE_I8 x
        | DV1.UVALUE_I32 x => DV2.UVALUE_I32 x
        | DV1.UVALUE_I64 x => DV2.UVALUE_I64 x
        | DV1.UVALUE_IPTR x =>
            let xz := LP1.IP.to_Z x in
            match LP2.IP.from_Z xz with
            | Oom msg => DV2.UVALUE_Oom DTYPE_IPTR
            | NoOom x' => DV2.UVALUE_IPTR x'
            end
        | DV1.UVALUE_Double x => DV2.UVALUE_Double x
        | DV1.UVALUE_Float x => DV2.UVALUE_Float x
        | DV1.UVALUE_Poison t => DV2.UVALUE_Poison t
        | DV1.UVALUE_Oom t => DV2.UVALUE_Oom t
        | DV1.UVALUE_None => DV2.UVALUE_None
        | DV1.UVALUE_Struct fields =>
            let fields' := map_In fields (fun elt HIn => uvalue_convert_lazy elt)in
            DV2.UVALUE_Struct fields'
        | DV1.UVALUE_Packed_struct fields =>
            let fields' := map_In fields (fun elt HIn => uvalue_convert_lazy elt)in
            DV2.UVALUE_Packed_struct fields'
        | DV1.UVALUE_Array elts =>
            let elts' := map_In elts (fun elt HIn => uvalue_convert_lazy elt)in
            DV2.UVALUE_Array elts'
        | DV1.UVALUE_Vector elts =>
            let elts' := map_In elts (fun elt HIn => uvalue_convert_lazy elt)in
            DV2.UVALUE_Vector elts'
        | DV1.UVALUE_Undef dt =>
            (* Could be a bit odd with intptr *)
            DV2.UVALUE_Undef dt
        | DV1.UVALUE_IBinop iop v1 v2 =>
            let v1' := uvalue_convert_lazy v1 in
            let v2' := uvalue_convert_lazy v2 in
            DV2.UVALUE_IBinop iop v1' v2'
        | DV1.UVALUE_ICmp cmp v1 v2 =>
            let v1' := uvalue_convert_lazy v1 in
            let v2' := uvalue_convert_lazy v2 in
            DV2.UVALUE_ICmp cmp v1' v2'
        | DV1.UVALUE_FBinop fop fm v1 v2 =>
            let v1' := uvalue_convert_lazy v1 in
            let v2' := uvalue_convert_lazy v2 in
            DV2.UVALUE_FBinop fop fm v1' v2'
        | DV1.UVALUE_FCmp cmp v1 v2 =>
            let v1' := uvalue_convert_lazy v1 in
            let v2' := uvalue_convert_lazy v2 in
            DV2.UVALUE_FCmp cmp v1' v2'
        | DV1.UVALUE_Conversion conv t_from v t_to =>
            let v' := uvalue_convert_lazy v in
            DV2.UVALUE_Conversion conv t_from v' t_to
        | DV1.UVALUE_GetElementPtr t ptrval idxs =>
            let ptrval' := uvalue_convert_lazy ptrval in
            let idxs' := map_In idxs (fun elt Hin => uvalue_convert_lazy elt) in
            DV2.UVALUE_GetElementPtr t ptrval' idxs'
        | DV1.UVALUE_ExtractElement t vec idx =>
            let vec' := uvalue_convert_lazy vec in
            let idx' := uvalue_convert_lazy idx in
            DV2.UVALUE_ExtractElement t vec' idx'
        | DV1.UVALUE_InsertElement t vec elt idx =>
            let vec' := uvalue_convert_lazy vec in
            let elt' := uvalue_convert_lazy elt in
            let idx' := uvalue_convert_lazy idx in
            DV2.UVALUE_InsertElement t vec' elt' idx'
        | DV1.UVALUE_ShuffleVector vec1 vec2 idxmask =>
            let vec1' := uvalue_convert_lazy vec1 in
            let vec2' := uvalue_convert_lazy vec2 in
            let idxmask' := uvalue_convert_lazy idxmask in
            DV2.UVALUE_ShuffleVector vec1' vec2' idxmask'
        | DV1.UVALUE_ExtractValue t vec idxs =>
            let vec' := uvalue_convert_lazy vec in
            DV2.UVALUE_ExtractValue t vec' idxs
        | DV1.UVALUE_InsertValue t vec elt idxs =>
            let vec' := uvalue_convert_lazy vec in
            let elt' := uvalue_convert_lazy elt in
            DV2.UVALUE_InsertValue t vec' elt' idxs
        | DV1.UVALUE_Select cnd v1 v2 =>
            let cnd' := uvalue_convert_lazy cnd in
            let v1' := uvalue_convert_lazy v1 in
            let v2' := uvalue_convert_lazy v2 in
            DV2.UVALUE_Select cnd' v1' v2'
        | DV1.UVALUE_ExtractByte uv dt idx sid =>
            let uv' := uvalue_convert_lazy uv in
            let idx' := uvalue_convert_lazy idx in
            DV2.UVALUE_ExtractByte uv' dt idx' sid
        | DV1.UVALUE_ConcatBytes uvs dt =>
            let uvs' := map_In uvs (fun elt Hin => uvalue_convert_lazy elt) in
            DV2.UVALUE_ConcatBytes uvs' dt
        end.
  
      Proof.
    (* intros uv. *)
    (* unfold uvalue_convert_lazy at 1. *)
    (* (* TODO: This is really slow *) *)
    (* rewrite Wf.WfExtensionality.fix_sub_eq_ext at 1. *)
    (* destruct uv; reflexivity. *)
  Admitted.

  Obligation Tactic :=
    try Tactics.program_simpl;
  try solve [ cbn; try lia
            | solve_dvalue_measure
            | solve_uvalue_measure
            | repeat split;
              intros * CONTRA;
              solve [inv CONTRA]
    ].

  Definition uvalue_converted_lazy (uv1 : DV1.uvalue) (uv2 : DV2.uvalue) : Prop :=
    uvalue_convert_lazy uv1 = uv2.

  Definition dvalue_converted_lazy (dv1 : DV1.dvalue) (dv2 : DV2.dvalue) : Prop :=
    dvalue_convert_lazy dv1 = dv2.

  
    (** A version of dvalue refinement between languages where OOM can be the lazy OOM value *)
  Program Fixpoint dvalue_refine_lazy (dv1 : DV1.dvalue) (dv2 : DV2.dvalue) {measure (DV1.dvalue_measure dv1)} : Prop
    := dvalue_converted_lazy dv1 dv2 \/
         match dv2 with
         | DV2.DVALUE_Oom t2 => DV1.dvalue_has_dtyp dv1 t2
         | DV2.DVALUE_Struct fields2 =>
             match dv1 with
             | DV1.DVALUE_Struct fields1 => Forall2_HIn fields1 fields2 (fun e1 e2 IN1 IN2 => dvalue_refine_lazy e1 e2)
             | _ => False
             end
         | DV2.DVALUE_Packed_struct fields2 =>
             match dv1 with
             | DV1.DVALUE_Packed_struct fields1 =>
                 Forall2_HIn fields1 fields2 (fun e1 e2 IN1 IN2 => dvalue_refine_lazy e1 e2)
             | _ => False
             end
         | DV2.DVALUE_Array elts2 =>
             match dv1 with 
             | DV1.DVALUE_Array elts1 =>
                 Forall2_HIn elts1 elts2 (fun e1 e2 IN1 IN2 => dvalue_refine_lazy e1 e2)
             | _ => False
             end
         | DV2.DVALUE_Vector elts2 =>
             match dv1 with 
             | DV1.DVALUE_Vector elts1 =>
                 Forall2_HIn elts1 elts2 (fun e1 e2 IN1 IN2 => dvalue_refine_lazy e1 e2)
             | _ => False
             end
         | _ => False
         end.

  Lemma dvalue_refine_lazy_equation :
    forall dv1 dv2,
      dvalue_refine_lazy dv1 dv2 =
        (dvalue_converted_lazy dv1 dv2 \/
         match dv2 with
         | DV2.DVALUE_Oom t2 => DV1.dvalue_has_dtyp dv1 t2
         | DV2.DVALUE_Struct fields2 =>
             match dv1 with
             | DV1.DVALUE_Struct fields1 => Forall2_HIn fields1 fields2 (fun e1 e2 IN1 IN2 => dvalue_refine_lazy e1 e2)
             | _ => False
             end
         | DV2.DVALUE_Packed_struct fields2 =>
             match dv1 with
             | DV1.DVALUE_Packed_struct fields1 =>
                 Forall2_HIn fields1 fields2 (fun e1 e2 IN1 IN2 => dvalue_refine_lazy e1 e2)
             | _ => False
             end
         | DV2.DVALUE_Array elts2 =>
             match dv1 with 
             | DV1.DVALUE_Array elts1 =>
                 Forall2_HIn elts1 elts2 (fun e1 e2 IN1 IN2 => dvalue_refine_lazy e1 e2)
             | _ => False
             end
         | DV2.DVALUE_Vector elts2 =>
             match dv1 with 
             | DV1.DVALUE_Vector elts1 =>
                 Forall2_HIn elts1 elts2 (fun e1 e2 IN1 IN2 => dvalue_refine_lazy e1 e2)
             | _ => False
             end
         | _ => False
         end).
  Proof.
    intros dv1 dv2.
    destruct dv2; Tactics.program_simpl.
    - destruct dv1.
      1 - 11 , 13 - 15: reflexivity.
      unfold dvalue_refine_lazy.
      unfold dvalue_refine_lazy_func.
      rewrite Wf.WfExtensionality.fix_sub_eq_ext at 1.
      reflexivity.
    - destruct dv1.
      1 - 12 , 14 - 15: reflexivity.
      unfold dvalue_refine_lazy.
      unfold dvalue_refine_lazy_func.
      rewrite Wf.WfExtensionality.fix_sub_eq_ext at 1.
      reflexivity.
    - destruct dv1.
      1 - 13 , 15: reflexivity.
      unfold dvalue_refine_lazy.
      unfold dvalue_refine_lazy_func.
      rewrite Wf.WfExtensionality.fix_sub_eq_ext at 1.
      reflexivity.
    - destruct dv1.
      1 - 14 : reflexivity.
      unfold dvalue_refine_lazy.
      unfold dvalue_refine_lazy_func.
      rewrite Wf.WfExtensionality.fix_sub_eq_ext at 1.
      reflexivity.
  Qed.

  Program Fixpoint uvalue_refine_lazy (uv1 : DV1.uvalue) (uv2 : DV2.uvalue) {measure (DV1.uvalue_measure uv1)} : Prop
    := uvalue_converted_lazy uv1 uv2 \/
         match uv2 with
         | DV2.UVALUE_Oom t2 => DV1.uvalue_has_dtyp uv1 t2
         | DV2.UVALUE_Struct fields2 =>
             match uv1 with
             | DV1.UVALUE_Struct fields1 => Forall2_HIn fields1 fields2 (fun e1 e2 IN1 IN2 => uvalue_refine_lazy e1 e2)
             | _ => False
             end
         | DV2.UVALUE_Packed_struct fields2 =>
             match uv1 with
             | DV1.UVALUE_Packed_struct fields1 =>
                 Forall2_HIn fields1 fields2 (fun e1 e2 IN1 IN2 => uvalue_refine_lazy e1 e2)
             | _ => False
             end
         | DV2.UVALUE_Array elts2 =>
             match uv1 with
             | DV1.UVALUE_Array elts1 => 
                 Forall2_HIn elts1 elts2 (fun e1 e2 IN1 IN2 => uvalue_refine_lazy e1 e2)
             | _ => False
             end
         | DV2.UVALUE_Vector elts2 =>
             match uv1 with
             | DV1.UVALUE_Vector elts1 => 
                 Forall2_HIn elts1 elts2 (fun e1 e2 IN1 IN2 => uvalue_refine_lazy e1 e2)
             | _ => False
             end
         | DV2.UVALUE_IBinop iop2 v1_2 v2_2 =>
             match uv1 with
             | DV1.UVALUE_IBinop iop1 v1_1 v2_1 => 
                 iop1 = iop2 /\
                   uvalue_refine_lazy v1_1 v1_2 /\
                   uvalue_refine_lazy v2_1 v2_2
             | _ => False
             end
         | DV2.UVALUE_ICmp cmp2 v1_2 v2_2 =>
             match uv1 with
             | DV1.UVALUE_ICmp cmp1 v1_1 v2_1 => 
                 cmp1 = cmp2 /\
                   uvalue_refine_lazy v1_1 v1_2 /\
                   uvalue_refine_lazy v2_1 v2_2
             | _ => False
             end
         | DV2.UVALUE_FBinop fop2 fm2 v1_2 v2_2 =>
             match uv1 with
             | DV1.UVALUE_FBinop fop1 fm1 v1_1 v2_1 => 
                 fop1 = fop2 /\
                   fm1 = fm2 /\
                   uvalue_refine_lazy v1_1 v1_2 /\
                   uvalue_refine_lazy v2_1 v2_2
             | _ => False
             end
         | DV2.UVALUE_FCmp cmp2 v1_2 v2_2 =>
             match uv1 with
             | DV1.UVALUE_FCmp cmp1 v1_1 v2_1 => 
                 cmp1 = cmp2 /\
                   uvalue_refine_lazy v1_1 v1_2 /\
                   uvalue_refine_lazy v2_1 v2_2
             | _ => False
             end
         | DV2.UVALUE_Conversion conv2 t_from2 v2 t_to2 =>
             match uv1 with
             | DV1.UVALUE_Conversion conv1 t_from1 v1 t_to1 => 
                 conv1 = conv2 /\
                   uvalue_refine_lazy v1 v2 /\
                   t_from1 = t_from2 /\
                   t_to1 = t_to2
             | _ => False
             end
         | DV2.UVALUE_GetElementPtr t2 ptrval2 idxs2 =>
             match uv1 with
             | DV1.UVALUE_GetElementPtr t1 ptrval1 idxs1 => 
                 t1 = t2 /\
                   uvalue_refine_lazy ptrval1 ptrval2 /\
                   Forall2_HIn idxs1 idxs2 (fun ix1 ix2 IN1 IN2 => uvalue_refine_lazy ix1 ix2)
             | _ => False
             end
         | DV2.UVALUE_ExtractElement vec_typ2 vec2 idx2 =>
             match uv1 with
             | DV1.UVALUE_ExtractElement vec_typ1 vec1 idx1 => 
                 vec_typ1 = vec_typ2 /\
                   uvalue_refine_lazy vec1 vec2 /\
                   uvalue_refine_lazy idx1 idx2
             | _ => False
             end
         | DV2.UVALUE_InsertElement vec_typ2 vec2 elt2 idx2 =>
             match uv1 with
             | DV1.UVALUE_InsertElement vec_typ1 vec1 elt1 idx1 => 
                 vec_typ1 = vec_typ2 /\
                   uvalue_refine_lazy vec1 vec2 /\
                   uvalue_refine_lazy elt1 elt2 /\
                   uvalue_refine_lazy idx1 idx2
             | _ => False
             end
         | DV2.UVALUE_ShuffleVector vec1_2 vec2_2 idxmask2 =>
             match uv1 with
             | DV1.UVALUE_ShuffleVector vec1_1 vec2_1 idxmask1 =>
                 uvalue_refine_lazy vec1_1 vec1_2 /\
                   uvalue_refine_lazy vec2_1 vec2_2 /\
                   uvalue_refine_lazy idxmask1 idxmask2
             | _ => False
             end
         | DV2.UVALUE_ExtractValue vec_typ2 vec2 idxs2 =>
             match uv1 with
             | DV1.UVALUE_ExtractValue vec_typ1 vec1 idxs1 => 
                 vec_typ1 = vec_typ2 /\
                   uvalue_refine_lazy vec1 vec2 /\
                   idxs1 = idxs2
             | _ => False
             end
         | DV2.UVALUE_InsertValue vec_typ2 vec2 elt2 idxs2 =>
             match uv1 with
             | DV1.UVALUE_InsertValue vec_typ1 vec1 elt1 idxs1 => 
                 vec_typ1 = vec_typ2 /\
                   uvalue_refine_lazy vec1 vec2 /\
                   uvalue_refine_lazy elt1 elt2 /\
                   idxs1 = idxs2
             | _ => False
             end
         | DV2.UVALUE_Select cnd2 v1_2 v2_2 =>
             match uv1 with
             | DV1.UVALUE_Select cnd1 v1_1 v2_1 => 
                 uvalue_refine_lazy cnd1 cnd2 /\
                   uvalue_refine_lazy v1_1 v1_2 /\
                   uvalue_refine_lazy v2_1 v2_2
             | _ => False
             end
         | DV2.UVALUE_ExtractByte uv2 dt2 idx2 sid2 =>
             match uv1 with
             | DV1.UVALUE_ExtractByte uv1 dt1 idx1 sid1 => 
                 uvalue_refine_lazy uv1 uv2 /\
                   dt1 = dt2 /\
                   uvalue_refine_lazy idx1 idx2 /\
                   sid1 = sid2
             | _ => False
             end
         | DV2.UVALUE_ConcatBytes uvs2 dt2 =>
             match uv1 with
             | DV1.UVALUE_ConcatBytes uvs1 dt1 => 
                 Forall2_HIn uvs1 uvs2 (fun uv1 uv2 IN1 IN2 => uvalue_refine_lazy uv1 uv2) /\
                   dt1 = dt2
             | _ => False
             end
         | _ => False
         end.
  Opaque uvalue_refine_lazy.

  Lemma uvalue_refine_lazy_equation :
    forall uv1 uv2,
      uvalue_refine_lazy uv1 uv2 =
        (uvalue_converted_lazy uv1 uv2 \/
                    match uv2 with
         | DV2.UVALUE_Oom t2 => DV1.uvalue_has_dtyp uv1 t2
         | DV2.UVALUE_Struct fields2 =>
             match uv1 with
             | DV1.UVALUE_Struct fields1 => Forall2_HIn fields1 fields2 (fun e1 e2 IN1 IN2 => uvalue_refine_lazy e1 e2)
             | _ => False
             end
         | DV2.UVALUE_Packed_struct fields2 =>
             match uv1 with
             | DV1.UVALUE_Packed_struct fields1 =>
                 Forall2_HIn fields1 fields2 (fun e1 e2 IN1 IN2 => uvalue_refine_lazy e1 e2)
             | _ => False
             end
         | DV2.UVALUE_Array elts2 =>
             match uv1 with
             | DV1.UVALUE_Array elts1 => 
                 Forall2_HIn elts1 elts2 (fun e1 e2 IN1 IN2 => uvalue_refine_lazy e1 e2)
             | _ => False
             end
         | DV2.UVALUE_Vector elts2 =>
             match uv1 with
             | DV1.UVALUE_Vector elts1 => 
                 Forall2_HIn elts1 elts2 (fun e1 e2 IN1 IN2 => uvalue_refine_lazy e1 e2)
             | _ => False
             end
         | DV2.UVALUE_IBinop iop2 v1_2 v2_2 =>
             match uv1 with
             | DV1.UVALUE_IBinop iop1 v1_1 v2_1 => 
                 iop1 = iop2 /\
                   uvalue_refine_lazy v1_1 v1_2 /\
                   uvalue_refine_lazy v2_1 v2_2
             | _ => False
             end
         | DV2.UVALUE_ICmp cmp2 v1_2 v2_2 =>
             match uv1 with
             | DV1.UVALUE_ICmp cmp1 v1_1 v2_1 => 
                 cmp1 = cmp2 /\
                   uvalue_refine_lazy v1_1 v1_2 /\
                   uvalue_refine_lazy v2_1 v2_2
             | _ => False
             end
         | DV2.UVALUE_FBinop fop2 fm2 v1_2 v2_2 =>
             match uv1 with
             | DV1.UVALUE_FBinop fop1 fm1 v1_1 v2_1 => 
                 fop1 = fop2 /\
                   fm1 = fm2 /\
                   uvalue_refine_lazy v1_1 v1_2 /\
                   uvalue_refine_lazy v2_1 v2_2
             | _ => False
             end
         | DV2.UVALUE_FCmp cmp2 v1_2 v2_2 =>
             match uv1 with
             | DV1.UVALUE_FCmp cmp1 v1_1 v2_1 => 
                 cmp1 = cmp2 /\
                   uvalue_refine_lazy v1_1 v1_2 /\
                   uvalue_refine_lazy v2_1 v2_2
             | _ => False
             end
         | DV2.UVALUE_Conversion conv2 t_from2 v2 t_to2 =>
             match uv1 with
             | DV1.UVALUE_Conversion conv1 t_from1 v1 t_to1 => 
                 conv1 = conv2 /\
                   uvalue_refine_lazy v1 v2 /\
                   t_from1 = t_from2 /\
                   t_to1 = t_to2
             | _ => False
             end
         | DV2.UVALUE_GetElementPtr t2 ptrval2 idxs2 =>
             match uv1 with
             | DV1.UVALUE_GetElementPtr t1 ptrval1 idxs1 => 
                 t1 = t2 /\
                   uvalue_refine_lazy ptrval1 ptrval2 /\
                   Forall2_HIn idxs1 idxs2 (fun ix1 ix2 IN1 IN2 => uvalue_refine_lazy ix1 ix2)
             | _ => False
             end
         | DV2.UVALUE_ExtractElement vec_typ2 vec2 idx2 =>
             match uv1 with
             | DV1.UVALUE_ExtractElement vec_typ1 vec1 idx1 => 
                 vec_typ1 = vec_typ2 /\
                   uvalue_refine_lazy vec1 vec2 /\
                   uvalue_refine_lazy idx1 idx2
             | _ => False
             end
         | DV2.UVALUE_InsertElement vec_typ2 vec2 elt2 idx2 =>
             match uv1 with
             | DV1.UVALUE_InsertElement vec_typ1 vec1 elt1 idx1 => 
                 vec_typ1 = vec_typ2 /\
                   uvalue_refine_lazy vec1 vec2 /\
                   uvalue_refine_lazy elt1 elt2 /\
                   uvalue_refine_lazy idx1 idx2
             | _ => False
             end
         | DV2.UVALUE_ShuffleVector vec1_2 vec2_2 idxmask2 =>
             match uv1 with
             | DV1.UVALUE_ShuffleVector vec1_1 vec2_1 idxmask1 =>
                 uvalue_refine_lazy vec1_1 vec1_2 /\
                   uvalue_refine_lazy vec2_1 vec2_2 /\
                   uvalue_refine_lazy idxmask1 idxmask2
             | _ => False
             end
         | DV2.UVALUE_ExtractValue vec_typ2 vec2 idxs2 =>
             match uv1 with
             | DV1.UVALUE_ExtractValue vec_typ1 vec1 idxs1 => 
                 vec_typ1 = vec_typ2 /\
                   uvalue_refine_lazy vec1 vec2 /\
                   idxs1 = idxs2
             | _ => False
             end
         | DV2.UVALUE_InsertValue vec_typ2 vec2 elt2 idxs2 =>
             match uv1 with
             | DV1.UVALUE_InsertValue vec_typ1 vec1 elt1 idxs1 => 
                 vec_typ1 = vec_typ2 /\
                   uvalue_refine_lazy vec1 vec2 /\
                   uvalue_refine_lazy elt1 elt2 /\
                   idxs1 = idxs2
             | _ => False
             end
         | DV2.UVALUE_Select cnd2 v1_2 v2_2 =>
             match uv1 with
             | DV1.UVALUE_Select cnd1 v1_1 v2_1 => 
                 uvalue_refine_lazy cnd1 cnd2 /\
                   uvalue_refine_lazy v1_1 v1_2 /\
                   uvalue_refine_lazy v2_1 v2_2
             | _ => False
             end
         | DV2.UVALUE_ExtractByte uv2 dt2 idx2 sid2 =>
             match uv1 with
             | DV1.UVALUE_ExtractByte uv1 dt1 idx1 sid1 => 
                 uvalue_refine_lazy uv1 uv2 /\
                   dt1 = dt2 /\
                   uvalue_refine_lazy idx1 idx2 /\
                   sid1 = sid2
             | _ => False
             end
         | DV2.UVALUE_ConcatBytes uvs2 dt2 =>
             match uv1 with
             | DV1.UVALUE_ConcatBytes uvs1 dt1 => 
                 Forall2_HIn uvs1 uvs2 (fun uv1 uv2 IN1 IN2 => uvalue_refine_lazy uv1 uv2) /\
                   dt1 = dt2
             | _ => False
             end
         | _ => False
         end).
  Proof.
    intros uv1 uv2.
    (* SAZ: These are a bit slow, but OK.
    destruct uv2; Tactics.program_simpl; destruct uv1; try reflexivity.
     *)
    (* TODO: each of the remaing goals follows from:
       
    unfold uvalue_refine_lazy at 1;
    unfold uvalue_refine_lazy_func;
    rewrite Wf.WfExtensionality.fix_sub_eq_ext at 1;
    reflexivity.
     *)
    admit.
  Admitted.

Lemma dvalue_refine_lazy_dvalue_convert_lazy :
    forall dv,
      dvalue_refine_lazy dv (dvalue_convert_lazy dv).
  Proof.
    intros dv.
    induction dv;
      rewrite dvalue_refine_lazy_equation;
      left; red; auto.
  Qed.

  Lemma uvalue_refine_lazy_uvalue_convert_lazy :
    forall dv,
      uvalue_refine_lazy dv (uvalue_convert_lazy dv).
  Proof.
    intros dv.
    induction dv;
      rewrite uvalue_refine_lazy_equation;
      left; red; auto.
  Qed.

  Lemma dvalue_refine_lazy_dvalue_converted_lazy :
    forall dv1 dv2,
      dvalue_converted_lazy dv1 dv2 ->
      dvalue_refine_lazy dv1 dv2.
  Proof.
    intros dv1 dv2 CONV; inv CONV.
    apply dvalue_refine_lazy_dvalue_convert_lazy.
  Qed.

  Lemma uvalue_refine_uvalue_converted :
    forall uv1 uv2,
      uvalue_converted_lazy uv1 uv2 ->
      uvalue_refine_lazy uv1 uv2.
  Proof.
    intros uv1 uv2 CONV; inv CONV.
    apply uvalue_refine_lazy_uvalue_convert_lazy.
  Qed.
*)
  Program Fixpoint dvalue_convert_strict (dv1 : DV1.dvalue) {measure (DV1.dvalue_measure dv1)} : OOM DV2.dvalue
    := match dv1 with
       | DV1.DVALUE_Addr a =>
           a' <- addr_convert a;;
           ret (DV2.DVALUE_Addr a')
       | DV1.DVALUE_I1 x  => ret (DV2.DVALUE_I1 x)
       | DV1.DVALUE_I8 x  => ret (DV2.DVALUE_I8 x)
       | DV1.DVALUE_I32 x => ret (DV2.DVALUE_I32 x)
       | DV1.DVALUE_I64 x => ret (DV2.DVALUE_I64 x)
       | DV1.DVALUE_IPTR x =>
           let xz := LP1.IP.to_Z x in
           x' <- LP2.IP.from_Z xz;;
           ret (DV2.DVALUE_IPTR x')
       | DV1.DVALUE_Double x => ret (DV2.DVALUE_Double x)
       | DV1.DVALUE_Float x => ret (DV2.DVALUE_Float x)
       | DV1.DVALUE_Oom t => ret (DV2.DVALUE_Oom t)
       | DV1.DVALUE_Poison t => ret (DV2.DVALUE_Poison t)
       | DV1.DVALUE_None => ret DV2.DVALUE_None
       | DV1.DVALUE_Struct fields =>
           fields' <- map_monad_InT fields (fun elt Hin => dvalue_convert_strict elt);;
           ret (DV2.DVALUE_Struct fields')
       | DV1.DVALUE_Packed_struct fields =>
           fields' <- map_monad_InT fields (fun elt Hin => dvalue_convert_strict elt);;
           ret (DV2.DVALUE_Packed_struct fields')
       | DV1.DVALUE_Array elts =>
           elts' <- map_monad_InT elts (fun elt Hin => dvalue_convert_strict elt);;
           ret (DV2.DVALUE_Array elts')
       | DV1.DVALUE_Vector elts =>
           elts' <- map_monad_InT elts (fun elt Hin => dvalue_convert_strict elt);;
           ret (DV2.DVALUE_Vector elts')
       end.


  Program Fixpoint uvalue_convert_strict (uv1 : DV1.uvalue) {measure (DV1.uvalue_measure uv1)} : OOM DV2.uvalue
    := match uv1 with
       | DV1.UVALUE_Addr a =>
           a' <- addr_convert a;;
           ret (DV2.UVALUE_Addr a')
       | DV1.UVALUE_I1 x  => ret (DV2.UVALUE_I1 x)
       | DV1.UVALUE_I8 x  => ret (DV2.UVALUE_I8 x)
       | DV1.UVALUE_I32 x => ret (DV2.UVALUE_I32 x)
       | DV1.UVALUE_I64 x => ret (DV2.UVALUE_I64 x)
       | DV1.UVALUE_IPTR x =>
           let xz := LP1.IP.to_Z x in
           x' <- LP2.IP.from_Z xz;;
           ret (DV2.UVALUE_IPTR x')
       | DV1.UVALUE_Double x => ret (DV2.UVALUE_Double x)
       | DV1.UVALUE_Float x => ret (DV2.UVALUE_Float x)
       | DV1.UVALUE_Oom t => ret (DV2.UVALUE_Oom t)
       | DV1.UVALUE_Poison t => ret (DV2.UVALUE_Poison t)
       | DV1.UVALUE_None => ret DV2.UVALUE_None
       | DV1.UVALUE_Struct fields =>
           fields' <- map_monad_InT fields (fun elt Hin => uvalue_convert_strict elt);;
           ret (DV2.UVALUE_Struct fields')
       | DV1.UVALUE_Packed_struct fields =>
           fields' <- map_monad_InT fields (fun elt Hin => uvalue_convert_strict elt);;
           ret (DV2.UVALUE_Packed_struct fields')
       | DV1.UVALUE_Array elts =>
           elts' <- map_monad_InT elts (fun elt Hin => uvalue_convert_strict elt);;
           ret (DV2.UVALUE_Array elts')
       | DV1.UVALUE_Vector elts =>
           elts' <- map_monad_InT elts (fun elt Hin => uvalue_convert_strict elt);;
           ret (DV2.UVALUE_Vector elts')
       | DV1.UVALUE_Undef dt =>
           (* Could be a bit odd with intptr *)
           ret (DV2.UVALUE_Undef dt)
       | DV1.UVALUE_IBinop iop v1 v2 =>
           v1' <- uvalue_convert_strict v1;;
           v2' <- uvalue_convert_strict v2;;
           ret (DV2.UVALUE_IBinop iop v1' v2')
       | DV1.UVALUE_ICmp cmp v1 v2 =>
           v1' <- uvalue_convert_strict v1;;
           v2' <- uvalue_convert_strict v2;;
           ret (DV2.UVALUE_ICmp cmp v1' v2')
       | DV1.UVALUE_FBinop fop fm v1 v2 =>
           v1' <- uvalue_convert_strict v1;;
           v2' <- uvalue_convert_strict v2;;
           ret (DV2.UVALUE_FBinop fop fm v1' v2')
       | DV1.UVALUE_FCmp cmp v1 v2 =>
           v1' <- uvalue_convert_strict v1;;
           v2' <- uvalue_convert_strict v2;;
           ret (DV2.UVALUE_FCmp cmp v1' v2')
       | DV1.UVALUE_Conversion conv t_from v t_to =>
           v' <- uvalue_convert_strict v;;
           ret (DV2.UVALUE_Conversion conv t_from v' t_to)
       | DV1.UVALUE_GetElementPtr t ptrval idxs =>
           ptrval' <- uvalue_convert_strict ptrval;;
           idxs' <- map_monad_InT idxs (fun elt Hin => uvalue_convert_strict elt);;
           ret (DV2.UVALUE_GetElementPtr t ptrval' idxs')
       | DV1.UVALUE_ExtractElement t vec idx =>
           vec' <- uvalue_convert_strict vec;;
           idx' <- uvalue_convert_strict idx;;
           ret (DV2.UVALUE_ExtractElement t vec' idx')
       | DV1.UVALUE_InsertElement t vec elt idx =>
           vec' <- uvalue_convert_strict vec;;
           elt' <- uvalue_convert_strict elt;;
           idx' <- uvalue_convert_strict idx;;
           ret (DV2.UVALUE_InsertElement t vec' elt' idx')
       | DV1.UVALUE_ShuffleVector vec1 vec2 idxmask =>
           vec1' <- uvalue_convert_strict vec1;;
           vec2' <- uvalue_convert_strict vec2;;
           idxmask' <- uvalue_convert_strict idxmask;;
           ret (DV2.UVALUE_ShuffleVector vec1' vec2' idxmask')
       | DV1.UVALUE_ExtractValue t vec idxs =>
           vec' <- uvalue_convert_strict vec;;
           ret (DV2.UVALUE_ExtractValue t vec' idxs)
       | DV1.UVALUE_InsertValue t vec elt idxs =>
           vec' <- uvalue_convert_strict vec;;
           elt' <- uvalue_convert_strict elt;;
           ret (DV2.UVALUE_InsertValue t vec' elt' idxs)
       | DV1.UVALUE_Select cnd v1 v2 =>
           cnd' <- uvalue_convert_strict cnd;;
           v1' <- uvalue_convert_strict v1;;
           v2' <- uvalue_convert_strict v2;;
           ret (DV2.UVALUE_Select cnd' v1' v2')
       | DV1.UVALUE_ExtractByte uv dt idx sid =>
           uv' <- uvalue_convert_strict uv;;
           idx' <- uvalue_convert_strict idx;;
           ret (DV2.UVALUE_ExtractByte uv' dt idx' sid)
       | DV1.UVALUE_ConcatBytes uvs dt =>
           uvs' <- map_monad_InT uvs (fun elt Hin => uvalue_convert_strict elt);;
           ret (DV2.UVALUE_ConcatBytes uvs' dt)
       end.

  Opaque dvalue_convert_strict.

    Lemma dvalue_convert_strict_equation :
    forall dv,
      dvalue_convert_strict dv =
        match dv with
        | DV1.DVALUE_Addr a =>
            a' <- addr_convert a;;
            ret (DV2.DVALUE_Addr a')
        | DV1.DVALUE_I1 x  => ret (DV2.DVALUE_I1 x)
        | DV1.DVALUE_I8 x  => ret (DV2.DVALUE_I8 x)
        | DV1.DVALUE_I32 x => ret (DV2.DVALUE_I32 x)
        | DV1.DVALUE_I64 x => ret (DV2.DVALUE_I64 x)
        | DV1.DVALUE_IPTR x =>
            let xz := LP1.IP.to_Z x in
            x' <- LP2.IP.from_Z xz;;
            ret (DV2.DVALUE_IPTR x')
        | DV1.DVALUE_Double x => ret (DV2.DVALUE_Double x)
        | DV1.DVALUE_Float x => ret (DV2.DVALUE_Float x)
        | DV1.DVALUE_Oom t => ret (DV2.DVALUE_Oom t)
        | DV1.DVALUE_Poison t => ret (DV2.DVALUE_Poison t)
        | DV1.DVALUE_None => ret DV2.DVALUE_None
        | DV1.DVALUE_Struct fields =>
            fields' <- map_monad_InT fields (fun elt Hin => dvalue_convert_strict elt);;
            ret (DV2.DVALUE_Struct fields')
        | DV1.DVALUE_Packed_struct fields =>
            fields' <- map_monad_InT fields (fun elt Hin => dvalue_convert_strict elt);;
            ret (DV2.DVALUE_Packed_struct fields')
        | DV1.DVALUE_Array elts =>
            elts' <- map_monad_InT elts (fun elt Hin => dvalue_convert_strict elt);;
            ret (DV2.DVALUE_Array elts')
        | DV1.DVALUE_Vector elts =>
            elts' <- map_monad_InT elts (fun elt Hin => dvalue_convert_strict elt);;
            ret (DV2.DVALUE_Vector elts')
        end.
  Proof.
    intros dv.
    Transparent dvalue_convert_strict.
    unfold dvalue_convert_strict at 1.
    rewrite Wf.WfExtensionality.fix_sub_eq_ext.
    destruct dv; reflexivity.
  Qed.

    Lemma uvalue_convert_strict_equation:
    forall uv,
      uvalue_convert_strict uv =
        match uv with
        | DV1.UVALUE_Addr a =>
            a' <- addr_convert a;;
            ret (DV2.UVALUE_Addr a')
        | DV1.UVALUE_I1 x  => ret (DV2.UVALUE_I1 x)
        | DV1.UVALUE_I8 x  => ret (DV2.UVALUE_I8 x)
        | DV1.UVALUE_I32 x => ret (DV2.UVALUE_I32 x)
        | DV1.UVALUE_I64 x => ret (DV2.UVALUE_I64 x)
        | DV1.UVALUE_IPTR x =>
            let xz := LP1.IP.to_Z x in
            x' <- LP2.IP.from_Z xz;;
            ret (DV2.UVALUE_IPTR x')
        | DV1.UVALUE_Double x => ret (DV2.UVALUE_Double x)
        | DV1.UVALUE_Float x => ret (DV2.UVALUE_Float x)
        | DV1.UVALUE_Oom t => ret (DV2.UVALUE_Oom t)
        | DV1.UVALUE_Poison t => ret (DV2.UVALUE_Poison t)
        | DV1.UVALUE_None => ret DV2.UVALUE_None
        | DV1.UVALUE_Struct fields =>
            fields' <- map_monad_InT fields (fun elt Hin => uvalue_convert_strict elt);;
            ret (DV2.UVALUE_Struct fields')
        | DV1.UVALUE_Packed_struct fields =>
            fields' <- map_monad_InT fields (fun elt Hin => uvalue_convert_strict elt);;
            ret (DV2.UVALUE_Packed_struct fields')
        | DV1.UVALUE_Array elts =>
            elts' <- map_monad_InT elts (fun elt Hin => uvalue_convert_strict elt);;
            ret (DV2.UVALUE_Array elts')
        | DV1.UVALUE_Vector elts =>
            elts' <- map_monad_InT elts (fun elt Hin => uvalue_convert_strict elt);;
            ret (DV2.UVALUE_Vector elts')
        | DV1.UVALUE_Undef dt =>
            (* Could be a bit odd with intptr *)
            ret (DV2.UVALUE_Undef dt)
        | DV1.UVALUE_IBinop iop v1 v2 =>
            v1' <- uvalue_convert_strict v1;;
            v2' <- uvalue_convert_strict v2;;
            ret (DV2.UVALUE_IBinop iop v1' v2')
        | DV1.UVALUE_ICmp cmp v1 v2 =>
            v1' <- uvalue_convert_strict v1;;
            v2' <- uvalue_convert_strict v2;;
            ret (DV2.UVALUE_ICmp cmp v1' v2')
        | DV1.UVALUE_FBinop fop fm v1 v2 =>
            v1' <- uvalue_convert_strict v1;;
            v2' <- uvalue_convert_strict v2;;
            ret (DV2.UVALUE_FBinop fop fm v1' v2')
        | DV1.UVALUE_FCmp cmp v1 v2 =>
            v1' <- uvalue_convert_strict v1;;
            v2' <- uvalue_convert_strict v2;;
            ret (DV2.UVALUE_FCmp cmp v1' v2')
        | DV1.UVALUE_Conversion conv t_from v t_to =>
            v' <- uvalue_convert_strict v;;
            ret (DV2.UVALUE_Conversion conv t_from v' t_to)
        | DV1.UVALUE_GetElementPtr t ptrval idxs =>
            ptrval' <- uvalue_convert_strict ptrval;;
            idxs' <- map_monad_InT idxs (fun elt Hin => uvalue_convert_strict elt);;
            ret (DV2.UVALUE_GetElementPtr t ptrval' idxs')
        | DV1.UVALUE_ExtractElement t vec idx =>
            vec' <- uvalue_convert_strict vec;;
            idx' <- uvalue_convert_strict idx;;
            ret (DV2.UVALUE_ExtractElement t vec' idx')
        | DV1.UVALUE_InsertElement t vec elt idx =>
            vec' <- uvalue_convert_strict vec;;
            elt' <- uvalue_convert_strict elt;;
            idx' <- uvalue_convert_strict idx;;
            ret (DV2.UVALUE_InsertElement t vec' elt' idx')
        | DV1.UVALUE_ShuffleVector vec1 vec2 idxmask =>
            vec1' <- uvalue_convert_strict vec1;;
            vec2' <- uvalue_convert_strict vec2;;
            idxmask' <- uvalue_convert_strict idxmask;;
            ret (DV2.UVALUE_ShuffleVector vec1' vec2' idxmask')
        | DV1.UVALUE_ExtractValue t vec idxs =>
            vec' <- uvalue_convert_strict vec;;
            ret (DV2.UVALUE_ExtractValue t vec' idxs)
        | DV1.UVALUE_InsertValue t vec elt idxs =>
            vec' <- uvalue_convert_strict vec;;
            elt' <- uvalue_convert_strict elt;;
            ret (DV2.UVALUE_InsertValue t vec' elt' idxs)
        | DV1.UVALUE_Select cnd v1 v2 =>
            cnd' <- uvalue_convert_strict cnd;;
            v1' <- uvalue_convert_strict v1;;
            v2' <- uvalue_convert_strict v2;;
            ret (DV2.UVALUE_Select cnd' v1' v2')
        | DV1.UVALUE_ExtractByte uv dt idx sid =>
            uv' <- uvalue_convert_strict uv;;
            idx' <- uvalue_convert_strict idx;;
            ret (DV2.UVALUE_ExtractByte uv' dt idx' sid)
        | DV1.UVALUE_ConcatBytes uvs dt =>
            uvs' <- map_monad_InT uvs (fun elt Hin => uvalue_convert_strict elt);;
            ret (DV2.UVALUE_ConcatBytes uvs' dt)
        end.
  Proof.
    (* intros uv. *)
    (* Transparent uvalue_convert_strict. *)
    (* unfold uvalue_convert_strict at 1. *)
    (* Opaque uvalue_convert_strict. *)
    (* (* TODO: This is really slow *) *)
    (* rewrite Wf.WfExtensionality.fix_sub_eq_ext. *)
    (* destruct uv; reflexivity. *)
  Admitted.



  Definition dvalue_refine_strict (dv1 : DV1.dvalue) (dv2 : DV2.dvalue) : Prop
    := dvalue_convert_strict dv1 = NoOom dv2.

  Definition uvalue_refine_strict (uv1 : DV1.uvalue) (uv2 : DV2.uvalue) : Prop
    := uvalue_convert_strict uv1 = NoOom uv2.

  Lemma dvalue_refine_strict_equation :
    forall (dv1 : DV1.dvalue) (dv2 : DV2.dvalue),
      dvalue_refine_strict dv1 dv2 = (dvalue_convert_strict dv1 = NoOom dv2).
  Proof.
    intros dv1 dv2.
    reflexivity.
  Qed.

  Lemma uvalue_refine_strict_equation :
    forall (uv1 : DV1.uvalue) (uv2 : DV2.uvalue),
      uvalue_refine_strict uv1 uv2 = (uvalue_convert_strict uv1 = NoOom uv2).
  Proof.
    reflexivity.
  Qed.

(*
  Lemma uvalue_convert_lazy_dv_to_uv_dvalue_convert_lazy :
    forall dv,
      uvalue_convert_lazy (DV1.dvalue_to_uvalue dv) = DV2.dvalue_to_uvalue (dvalue_convert_lazy dv).
  Proof.
    intros dv.
    rewrite uvalue_convert_lazy_equation.
    rewrite dvalue_convert_lazy_equation.
    induction dv; try solve [ cbn; auto
                            | Tactics.program_simpl; break_match; reflexivity 
                    ].

    { (* Structs *)
      Tactics.program_simpl.
      induction fields.
      - cbn; auto.
      - rewrite map_In_cons, map_cons.
        rewrite map_In_cons, map_cons.

        forward IHfields.
        { intros u IN.
          apply H; cbn; auto.
        }

        inv IHfields.
        rewrite uvalue_convert_lazy_equation.
        rewrite dvalue_convert_lazy_equation.
        rewrite H; cbn; auto.
    }

    { (* Packed structs *)
      Tactics.program_simpl.
      induction fields.
      - cbn; auto.
      - rewrite map_In_cons, map_cons.
        rewrite map_In_cons, map_cons.

        forward IHfields.
        { intros u IN.
          apply H; cbn; auto.
        }

        inv IHfields.
        rewrite uvalue_convert_lazy_equation.
        rewrite dvalue_convert_lazy_equation.
        rewrite H; cbn; auto.
    }

    { (* Arrays *)
      Tactics.program_simpl.
      induction elts.
      - cbn; auto.
      - rewrite map_In_cons, map_cons.
        rewrite map_In_cons, map_cons.

        forward IHelts.
        { intros u IN.
          apply H; cbn; auto.
        }

        inv IHelts.
        rewrite uvalue_convert_lazy_equation.
        rewrite dvalue_convert_lazy_equation.
        rewrite H; cbn; auto.
    }

    { (* Vectors *)
      Tactics.program_simpl.
      induction elts.
      - cbn; auto.
      - rewrite map_In_cons, map_cons.
        rewrite map_In_cons, map_cons.

        forward IHelts.
        { intros u IN.
          apply H; cbn; auto.
        }

        inv IHelts.
        rewrite uvalue_convert_lazy_equation.
        rewrite dvalue_convert_lazy_equation.
        rewrite H; cbn; auto.
    }
  Qed.

  Lemma dvalue_refine_lazy_dvalue_to_uvalue :
    forall dv1 dv2,
      dvalue_refine_lazy dv1 dv2 ->
      uvalue_refine_lazy (DV1.dvalue_to_uvalue dv1) (DV2.dvalue_to_uvalue dv2).
  Proof.
    induction dv1; intros dv2 REF.
    1-11: solve [
        rewrite dvalue_refine_lazy_equation in REF;
        unfold dvalue_converted_lazy in *;
        rewrite dvalue_convert_lazy_equation in REF;
        rewrite uvalue_refine_lazy_equation;
        cbn in *; unfold uvalue_converted_lazy in *;
        rewrite uvalue_convert_lazy_equation; cbn in *;
        solve
          [ (cbn in REF;
             destruct REF as [REF | REF];
             [ subst; auto
             | destruct dv2; inv REF;
               unfold DV2.dvalue_to_uvalue;
               try solve [auto | right; constructor; auto]
            ])
          | break_match_hyp;
            (cbn in REF;
             destruct REF as [REF | REF];
             [ subst; auto
             | destruct dv2; inv REF;
               unfold DV2.dvalue_to_uvalue;
               try solve [auto | right; constructor; auto]
            ])
          ]
      ].

    { rewrite dvalue_refine_lazy_equation in REF;
        unfold dvalue_converted_lazy in *;
        rewrite dvalue_convert_lazy_equation in REF.

      destruct REF as [REF | REF].
      - subst; auto.
        rewrite uvalue_refine_lazy_equation.
        left.
        cbn.

        induction fields.
        + cbn. unfold uvalue_converted_lazy. rewrite uvalue_convert_lazy_equation. cbn. reflexivity.
        + rewrite map_cons, map_In_cons.
          unfold uvalue_converted_lazy in *;
          rewrite uvalue_convert_lazy_equation in IHfields.
          rewrite uvalue_convert_lazy_equation.
          rewrite map_In_cons, map_cons.

          forward IHfields.
          { intros u H0 dv2 H1.
            apply H; cbn; auto.
          }

          inv IHfields.

          assert
            (uvalue_convert_lazy (DV1.dvalue_to_uvalue a) = DV2.dvalue_to_uvalue (dvalue_convert_lazy a)).
          { apply uvalue_convert_lazy_dv_to_uv_dvalue_convert_lazy.
          }

          rewrite H0.
          reflexivity.
      - destruct dv2; try solve [inv REF].
        + (* OOM *)
          cbn.
          rewrite uvalue_refine_lazy_equation.
          inv REF.
          * right; constructor; auto.
          * (* Struct *)
            right.
            cbn.
            constructor.
            { apply DV1.dvalue_to_uvalue_preserves_dtyp; auto.
            }
            { pose proof (DV1.dvalue_to_uvalue_preserves_dtyp H2).
              inv H0.
              - constructor.
              - cbn. constructor; auto.
            }
        + (* Struct *)
          rewrite uvalue_refine_lazy_equation.
          right.
          unfold DV1.dvalue_to_uvalue at 1.
          unfold DV2.dvalue_to_uvalue at  1.
          cbn.

          induction fields, fields0; inversion REF.
          { cbn; auto. }
          { rewrite map_cons.
            rewrite map_cons.
            repeat fold DV2.dvalue_to_uvalue in *.
            apply Forall2_HIn_cons.
            apply H; cbn; auto.

            apply Forall2_HIn_forall.
            apply Forall2_HIn_forall in H1 as [LEN H1].
            split.
            - repeat rewrite map_length. auto.
            - intros i a0 b NA NB.
              eexists.
              eapply Util.Nth_In; eauto.
              eexists.
              eapply Util.Nth_In; eauto.

              pose proof NA as NA'.
              pose proof NB as NB'.
              apply Nth_map_iff in NA', NB'.
              destruct NA' as [a' [DVA' NA']].
              destruct NB' as [b' [DVB' NB']].

              apply Util.Nth_In in NA, NB.
              apply in_map_iff in NA, NB.
              destruct NA as [dv1 [DV1 IN1]].
              destruct NB as [dv2 [DV2 IN2]].
              subst.
              apply H.
              right; auto.

              pose proof (H1 _ _ _ NA' NB') as [IN1' [IN2' REF']].
              apply DV2.dvalue_to_uvalue_inj in DVB'; subst.
              apply DV1.dvalue_to_uvalue_inj in DVA'; subst.
              auto.
          }
    }

    { rewrite dvalue_refine_lazy_equation in REF;
        unfold dvalue_converted_lazy in *;
        rewrite dvalue_convert_lazy_equation in REF.

      destruct REF as [REF | REF].
      - subst; auto.
        rewrite uvalue_refine_lazy_equation.
        left.
        cbn.

        induction fields.
        + cbn. unfold uvalue_converted_lazy. rewrite uvalue_convert_lazy_equation. reflexivity.
        + rewrite map_cons, map_In_cons.
          unfold uvalue_converted_lazy in *.
          rewrite uvalue_convert_lazy_equation in IHfields.
          rewrite uvalue_convert_lazy_equation.
          rewrite map_In_cons, map_cons.

          forward IHfields.
          { intros u H0 dv2 H1.
            apply H; cbn; auto.
          }

          inv IHfields.

          assert
            (uvalue_convert_lazy (DV1.dvalue_to_uvalue a) = DV2.dvalue_to_uvalue (dvalue_convert_lazy a)).
          { apply uvalue_convert_lazy_dv_to_uv_dvalue_convert_lazy.
          }

          rewrite H0.
          reflexivity.
      - destruct dv2; try solve [inv REF].
        + (* OOM *)
          cbn. rewrite uvalue_refine_lazy_equation.  inv REF.
          * right; constructor; auto.
          * (* Struct *)
            right.
            cbn.
            constructor.
            { apply DV1.dvalue_to_uvalue_preserves_dtyp; auto.
            }
            { pose proof (DV1.dvalue_to_uvalue_preserves_dtyp H2).
              inv H0.
              - constructor.
              - cbn. constructor; auto.
            }
        + (* Struct *)
          rewrite uvalue_refine_lazy_equation.
          right.
          unfold DV1.dvalue_to_uvalue at 1.
          unfold DV2.dvalue_to_uvalue at  1.
          cbn.

          induction fields, fields0; inversion REF.
          { cbn; auto. }
          { rewrite map_cons.
            rewrite map_cons.
            repeat fold DV2.dvalue_to_uvalue in *.
            repeat fold DV1.dvalue_to_uvalue in *.
            apply Forall2_HIn_cons.
            apply H; cbn; auto.

            apply Forall2_HIn_forall.
            apply Forall2_HIn_forall in H1 as [LEN H1].
            split.
            - repeat rewrite map_length. auto.
            - intros i a0 b NA NB.
              eexists.
              eapply Util.Nth_In; eauto.
              eexists.
              eapply Util.Nth_In; eauto.

              pose proof NA as NA'.
              pose proof NB as NB'.
              apply Nth_map_iff in NA', NB'.
              destruct NA' as [a' [DVA' NA']].
              destruct NB' as [b' [DVB' NB']].

              apply Util.Nth_In in NA, NB.
              apply in_map_iff in NA, NB.
              destruct NA as [dv1 [DV1 IN1]].
              destruct NB as [dv2 [DV2 IN2]].
              subst.
              apply H.
              right; auto.

              pose proof (H1 _ _ _ NA' NB') as [IN1' [IN2' REF']].
              apply DV2.dvalue_to_uvalue_inj in DVB'; subst.
              apply DV1.dvalue_to_uvalue_inj in DVA'; subst.
              auto.
          }
    }

    { rewrite dvalue_refine_lazy_equation in REF;
        unfold dvalue_converted_lazy in *; rewrite dvalue_convert_lazy_equation in REF.

      destruct REF as [REF | REF].
      - subst; auto.
        rewrite uvalue_refine_lazy_equation.
        left.
        cbn.

        rename elts into fields.
        induction fields.
        + cbn.  unfold uvalue_converted_lazy.
          rewrite uvalue_convert_lazy_equation. reflexivity.
        + rewrite map_cons, map_In_cons.
          unfold uvalue_converted_lazy in *.
          rewrite uvalue_convert_lazy_equation in IHfields.
          rewrite uvalue_convert_lazy_equation.
          rewrite map_In_cons, map_cons.

          forward IHfields.
          { intros u H0 dv2 H1.
            apply H; cbn; auto.
          }

          inv IHfields.

          assert
            (uvalue_convert_lazy (DV1.dvalue_to_uvalue a) = DV2.dvalue_to_uvalue (dvalue_convert_lazy a)).
          { apply uvalue_convert_lazy_dv_to_uv_dvalue_convert_lazy.
          }

          rewrite H0.
          reflexivity.
      - destruct dv2; try solve [inv REF].
        + (* OOM *)
          cbn. inv REF.
          rewrite uvalue_refine_lazy_equation.
          right.
          constructor.
          * apply Forall_forall.
            intros x IN.
            apply in_map_iff in IN as [x' [CONV IN]].
            apply Forall_forall with (x:=x') in H1; auto.
            subst.
            apply DV1.dvalue_to_uvalue_preserves_dtyp; auto.
          * rewrite map_length; auto.
        + (* Struct *)
          rewrite uvalue_refine_lazy_equation.
          right.
          unfold DV1.dvalue_to_uvalue at 1.
          unfold DV2.dvalue_to_uvalue at 1.
          cbn. 
          repeat fold DV2.dvalue_to_uvalue in *.
          repeat fold DV1.dvalue_to_uvalue in *.

          induction elts, elts0; inversion REF.
          { cbn; auto. }
          { rewrite map_cons.
            rewrite map_cons.
            apply Forall2_HIn_cons.
            apply H; cbn; auto.

            apply Forall2_HIn_forall.
            apply Forall2_HIn_forall in H1 as [LEN H1].
            split.
            - repeat rewrite map_length. auto.
            - intros i a0 b NA NB.
              eexists.
              eapply Util.Nth_In; eauto.
              eexists.
              eapply Util.Nth_In; eauto.

              pose proof NA as NA'.
              pose proof NB as NB'.
              apply Nth_map_iff in NA', NB'.
              destruct NA' as [a' [DVA' NA']].
              destruct NB' as [b' [DVB' NB']].

              apply Util.Nth_In in NA, NB.
              apply in_map_iff in NA, NB.
              destruct NA as [dv1 [DV1 IN1]].
              destruct NB as [dv2 [DV2 IN2]].
              subst.
              apply H.
              right; auto.

              pose proof (H1 _ _ _ NA' NB') as [IN1' [IN2' REF']].
              apply DV2.dvalue_to_uvalue_inj in DVB'; subst.
              apply DV1.dvalue_to_uvalue_inj in DVA'; subst.
              auto.
          }
    }

    { rewrite dvalue_refine_lazy_equation in REF;
        unfold dvalue_converted_lazy in *; rewrite dvalue_convert_lazy_equation in REF.
      destruct REF as [REF | REF].
      - subst; auto.
        rewrite uvalue_refine_lazy_equation.
        left.
        cbn.
        rename elts into fields.
        induction fields.
        + cbn. unfold uvalue_converted_lazy. rewrite uvalue_convert_lazy_equation. reflexivity.
        + rewrite map_cons, map_In_cons.
          unfold uvalue_converted_lazy in *.
          rewrite uvalue_convert_lazy_equation in IHfields.
          rewrite uvalue_convert_lazy_equation.
          rewrite map_In_cons, map_cons.
          forward IHfields.
          { intros u H0 dv2 H1.
            apply H; cbn; auto.
          }
          inv IHfields.
          assert
            (uvalue_convert_lazy (DV1.dvalue_to_uvalue a) = DV2.dvalue_to_uvalue (dvalue_convert_lazy a)).
          { apply uvalue_convert_lazy_dv_to_uv_dvalue_convert_lazy.
          }

          rewrite H0.
          reflexivity.
      - destruct dv2; try solve [inv REF].
        + (* OOM *)
          cbn. inv REF.
          rewrite uvalue_refine_lazy_equation.
          right.
          constructor.
          * apply Forall_forall.
            intros x IN.
            apply in_map_iff in IN as [x' [CONV IN]].
            apply Forall_forall with (x:=x') in H1; auto.
            subst.
            apply DV1.dvalue_to_uvalue_preserves_dtyp; auto.
          * rewrite map_length; auto.
          * auto.
        + (* Struct *)
          rewrite uvalue_refine_lazy_equation.
          right.
          unfold DV1.dvalue_to_uvalue at 1.
          unfold DV2.dvalue_to_uvalue at 1.
          cbn. 
          repeat fold DV2.dvalue_to_uvalue in *.
          repeat fold DV1.dvalue_to_uvalue in *.

          induction elts, elts0; inversion REF.
          { cbn; auto.
          }
          { rewrite map_cons.
            rewrite map_cons.
            apply Forall2_HIn_cons.
            apply H; cbn; auto.

            apply Forall2_HIn_forall.
            apply Forall2_HIn_forall in H1 as [LEN H1].
            split.
            - repeat rewrite map_length. auto.
            - intros i a0 b NA NB.
              eexists.
              eapply Util.Nth_In; eauto.
              eexists.
              eapply Util.Nth_In; eauto.

              pose proof NA as NA'.
              pose proof NB as NB'.
              apply Nth_map_iff in NA', NB'.
              destruct NA' as [a' [DVA' NA']].
              destruct NB' as [b' [DVB' NB']].

              apply Util.Nth_In in NA, NB.
              apply in_map_iff in NA, NB.
              destruct NA as [dv1 [DV1 IN1]].
              destruct NB as [dv2 [DV2 IN2]].
              subst.
              apply H.
              right; auto.

              pose proof (H1 _ _ _ NA' NB') as [IN1' [IN2' REF']].
              apply DV2.dvalue_to_uvalue_inj in DVB'; subst.
              apply DV1.dvalue_to_uvalue_inj in DVA'; subst.
              auto.
          }
    }
  Qed.

  Hint Resolve dvalue_refine_lazy_dvalue_to_uvalue : DVALUE_REFINE.

  #[global] Opaque dvalue_convert_lazy.
  #[global] Opaque uvalue_convert_lazy.
  #[global] Opaque dvalue_refine_lazy.
  #[global] Opaque uvalue_refine_lazy.
 *)

  #[global] Opaque dvalue_convert_strict.
  #[global] Opaque uvalue_convert_strict.
  #[global] Opaque dvalue_refine_strict.
  #[global] Opaque uvalue_refine_strict.

  (* START AT A FASTER PROOF:
    intros dv1 dv2 REF.
    rewrite dvalue_refine_strict_equation in REF.
    rewrite dvalue_convert_strict_equation in REF.
    revert dv2 REF.
    induction dv1; intros dv2 REF.

    1-11:
      cbn in REF;
      rewrite uvalue_refine_strict_equation;
      rewrite uvalue_convert_strict_equation.
    1-11:
      solve
        [ cbn; break_match_hyp; inv REF; auto
        | inv REF; auto
        ].

    { cbn.
      rewrite uvalue_refine_strict_equation.
      rewrite uvalue_convert_strict_equation.
      induction fields; simpl in *.
      - inversion REF; subst. 
        Tactics.program_simpl.
      - break_match_goal; break_match_hyp. simpl in *.
      
      break_match_goal; break_match_hyp; inv REF.
      - Tactics.program_simpl.
        revert l0 Heqo0 l Heqo. induction fields; intros l0 Heqo0 l Heqo.
        + cbn in *.
          inv Heqo0; inv Heqo.
          reflexivity.
        + rewrite map_cons, map_monad_InT_unfold in Heqo.
          rewrite map_monad_InT_unfold in Heqo0.
          cbn in *.

          destruct (dvalue_convert_strict a) eqn:CONVA; inv Heqo0.
          pose proof H as IH.
          specialize (H a (or_introl eq_refl) d).
          forward H.
          rewrite dvalue_refine_strict_equation in *; auto.
          rewrite uvalue_refine_strict_equation in *.
          rewrite H in Heqo.

          break_match_hyp; inv H1.
          break_match_hyp; inv Heqo.

          cbn.

          forward IHfields.
          { intros u H0 dv2 H1.
            auto.
          }
          specialize (IHfields l1 eq_refl l0 eq_refl).

          inv IHfields.
          auto.
*)
  
  (* TODO: This seems better than lazy proof... Can probably do the same? *)
  Lemma dvalue_refine_strict_dvalue_to_uvalue :
    forall dv1 dv2,
      dvalue_refine_strict dv1 dv2 ->
      uvalue_refine_strict (DV1.dvalue_to_uvalue dv1) (DV2.dvalue_to_uvalue dv2).
  Proof.
   induction dv1; intros dv2 REF;
      rewrite dvalue_refine_strict_equation in REF;
      rewrite dvalue_convert_strict_equation in REF;
      rewrite uvalue_refine_strict_equation;
      cbn in *;
      rewrite uvalue_convert_strict_equation; cbn in *.

    1-11:
      solve
        [ break_match_hyp; inv REF; auto
        | inv REF; auto
        ].

    { (* Structures *)
      break_match_goal; break_match_hyp; inv REF.
      - Tactics.program_simpl.
        revert l0 Heqo0 l Heqo. induction fields; intros l0 Heqo0 l Heqo.
        + cbn in *.
          inv Heqo0; inv Heqo.
          reflexivity.
        + rewrite map_cons, map_monad_InT_unfold in Heqo.
          rewrite map_monad_InT_unfold in Heqo0.
          cbn in *.

          destruct (dvalue_convert_strict a) eqn:CONVA; inv Heqo0.
          pose proof H as IH.
          specialize (H a (or_introl eq_refl) d).
          forward H.
          rewrite dvalue_refine_strict_equation in *; auto.
          rewrite uvalue_refine_strict_equation in *.
          rewrite H in Heqo.

          break_match_hyp; inv H1.
          break_match_hyp; inv Heqo.

          cbn.

          forward IHfields.
          { intros u H0 dv2 H1.
            auto.
          }
          specialize (IHfields l1 eq_refl l0 eq_refl).

          inv IHfields.
          auto.
      - cbn.
        eapply map_monad_InT_OOM_fail in Heqo.
        destruct Heqo as [a [INA Heqo]].

        pose proof INA as INA'.
        apply InT_Nth in INA' as [i NTHA].
        pose proof NTHA as NTHA'.
        apply Nth_map_iff in NTHA'.
        destruct NTHA' as [x [A NTHX]].
        pose proof NTHX as INX.
        apply Nth_InT in INX.

        pose proof Heqo0 as SUC.
        apply map_monad_InT_OOM_succeeds' with (a:=x) in SUC; auto.
        destruct SUC as [b CONVX].

        setoid_rewrite dvalue_refine_strict_equation in H.
        pose proof H as IH.
        specialize (H x (In_InT _ _ INX) b CONVX).

        rewrite A in H.
        rewrite uvalue_refine_strict_equation in H.
        rewrite H in Heqo.
        inv Heqo.
    }
    
    { (* Packed Structures *)
      break_match_goal; break_match_hyp; inv REF.
      - revert l0 Heqo0 l Heqo. induction fields; intros l0 Heqo0 l Heqo.
        + cbn in *.
          inv Heqo0; inv Heqo.
          reflexivity.
        + rewrite map_cons, map_monad_InT_unfold in Heqo.
          rewrite map_monad_InT_unfold in Heqo0.
          cbn in *.

          destruct (dvalue_convert_strict a) eqn:CONVA; inv Heqo0.
          pose proof H as IH.
          specialize (H a (or_introl eq_refl) d).
          forward H.
          rewrite dvalue_refine_strict_equation in *; auto.
          rewrite uvalue_refine_strict_equation in *.
          rewrite H in Heqo.

          break_match_hyp; inv H1.
          break_match_hyp; inv Heqo.

          cbn.

          forward IHfields.
          { intros u H0 dv2 H1.
            auto.
          }
          specialize (IHfields l1 eq_refl l0 eq_refl).

          inv IHfields.
          auto.
      - cbn.

        eapply map_monad_InT_OOM_fail in Heqo.
        destruct Heqo as [a [INA Heqo]].

        pose proof INA as INA'.
        apply InT_Nth in INA' as [i NTHA].
        pose proof NTHA as NTHA'.
        apply Nth_map_iff in NTHA'.
        destruct NTHA' as [x [A NTHX]].
        pose proof NTHX as INX.
        apply Nth_InT in INX.

        pose proof Heqo0 as SUC.
        apply map_monad_InT_OOM_succeeds' with (a:=x) in SUC; auto.
        destruct SUC as [b CONVX].

        setoid_rewrite dvalue_refine_strict_equation in H.
        pose proof H as IH.
        specialize (H x (In_InT _ _ INX) b CONVX).

        rewrite A in H.
        rewrite uvalue_refine_strict_equation in H.
        rewrite H in Heqo.
        inv Heqo.
    }

    { (* Arrays *)
      break_match_goal; break_match_hyp; inv REF.
      - revert l0 Heqo0 l Heqo. induction elts; intros l0 Heqo0 l Heqo.
        + cbn in *.
          inv Heqo0; inv Heqo.
          reflexivity.
        + rewrite map_cons, map_monad_InT_unfold in Heqo.
          rewrite map_monad_InT_unfold in Heqo0.
          cbn in *.

          destruct (dvalue_convert_strict a) eqn:CONVA; inv Heqo0.
          pose proof H as IH.
          specialize (H a (or_introl eq_refl) d).
          forward H.
          rewrite dvalue_refine_strict_equation in *; auto.
          rewrite uvalue_refine_strict_equation in *.
          rewrite H in Heqo.

          break_match_hyp; inv H1.
          break_match_hyp; inv Heqo.

          cbn.

          forward IHelts.
          { intros u H0 dv2 H1.
            auto.
          }
          specialize (IHelts l1 eq_refl l0 eq_refl).

          inv IHelts.
          auto.
      - cbn.

        eapply map_monad_InT_OOM_fail in Heqo.
        destruct Heqo as [a [INA Heqo]].

        pose proof INA as INA'.
        apply InT_Nth in INA' as [i NTHA].
        pose proof NTHA as NTHA'.
        apply Nth_map_iff in NTHA'.
        destruct NTHA' as [x [A NTHX]].
        pose proof NTHX as INX.
        apply Nth_InT in INX.

        pose proof Heqo0 as SUC.
        apply map_monad_InT_OOM_succeeds' with (a:=x) in SUC; auto.
        destruct SUC as [b CONVX].

        setoid_rewrite dvalue_refine_strict_equation in H.
        pose proof H as IH.
        specialize (H x (In_InT _ _ INX) b CONVX).

        rewrite A in H.
        rewrite uvalue_refine_strict_equation in H.
        rewrite H in Heqo.
        inv Heqo.
    }

    { (* Vectors *)
      break_match_goal; break_match_hyp; inv REF.
      - revert l0 Heqo0 l Heqo. induction elts; intros l0 Heqo0 l Heqo.
        + cbn in *.
          inv Heqo0; inv Heqo.
          reflexivity.
        + rewrite map_cons, map_monad_InT_unfold in Heqo.
          rewrite map_monad_InT_unfold in Heqo0.
          cbn in *.

          destruct (dvalue_convert_strict a) eqn:CONVA; inv Heqo0.
          pose proof H as IH.
          specialize (H a (or_introl eq_refl) d).
          forward H.
          rewrite dvalue_refine_strict_equation in *; auto.
          rewrite uvalue_refine_strict_equation in *.
          rewrite H in Heqo.

          break_match_hyp; inv H1.
          break_match_hyp; inv Heqo.

          cbn.

          forward IHelts.
          { intros u H0 dv2 H1.
            auto.
          }
          specialize (IHelts l1 eq_refl l0 eq_refl).

          inv IHelts.
          auto.
      - cbn.

        eapply map_monad_InT_OOM_fail in Heqo.
        destruct Heqo as [a [INA Heqo]].

        pose proof INA as INA'.
        apply InT_Nth in INA' as [i NTHA].
        pose proof NTHA as NTHA'.
        apply Nth_map_iff in NTHA'.
        destruct NTHA' as [x [A NTHX]].
        pose proof NTHX as INX.
        apply Nth_InT in INX.

        pose proof Heqo0 as SUC.
        apply map_monad_InT_OOM_succeeds' with (a:=x) in SUC; auto.
        destruct SUC as [b CONVX].

        setoid_rewrite dvalue_refine_strict_equation in H.
        pose proof H as IH.
        specialize (H x (In_InT _ _ INX) b CONVX).

        rewrite A in H.
        rewrite uvalue_refine_strict_equation in H.
        rewrite H in Heqo.
        inv Heqo.
    }
  Qed.

  Hint Resolve dvalue_refine_strict_dvalue_to_uvalue : DVALUE_REFINE.

  (* TODO: Move this? *)
  Ltac unfold_dvalue_refine_strict :=
    rewrite dvalue_refine_strict_equation, dvalue_convert_strict_equation in *.

  Ltac unfold_dvalue_refine_strict_goal :=
    rewrite dvalue_refine_strict_equation, dvalue_convert_strict_equation.

  Ltac unfold_dvalue_refine_strict_in H :=
    rewrite dvalue_refine_strict_equation, dvalue_convert_strict_equation in H.

  Ltac unfold_uvalue_refine_strict :=
    rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation in *.

  Ltac unfold_uvalue_refine_strict_goal :=
    rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.

  Ltac unfold_uvalue_refine_strict_in H :=
    rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation in H.

  Ltac solve_uvalue_refine_strict :=
    solve [unfold_uvalue_refine_strict;
           cbn;
           solve [ auto
                 | rewrite addr_convert_null;
                   reflexivity
             ]
      ].

  Ltac solve_dvalue_refine_strict :=
    solve [unfold_dvalue_refine_strict;
           cbn;
           solve [ auto
                 | rewrite addr_convert_null;
                   reflexivity
             ]
      ].

  (** Lemmas about is_concrete *)
(*
  Lemma uvalue_convert_lazy_preserves_is_concrete :
    forall uv uvc b,
      uvalue_convert_lazy uv = uvc ->
      DV1.is_concrete uv = b ->
      DV2.is_concrete uvc = b.
  Proof.
    induction uv using DV1.uvalue_ind';
      intros uvc b UVC CONC; cbn in *;
      rewrite uvalue_convert_lazy_equation in UVC;
      try solve
        [ cbn in *; subst; try break_match; cbn; auto
        ].

    - (* Structs *)
      rewrite map_In_cons in UVC.
      cbn in UVC.
      subst.
      cbn.
      destruct (DV1.is_concrete uv) eqn:HUV.
      + rewrite IHuv with (b:=true); auto.
        cbn.
        destruct (forallb DV1.is_concrete uvs) eqn:HUVS.
        * pose proof (IHuv0 (DV2.UVALUE_Struct (map_In uvs (fun x _ => uvalue_convert_lazy x))) true).
          forward H.
          rewrite uvalue_convert_lazy_equation; cbn; auto.
          forward H; auto.
        * pose proof (IHuv0 (DV2.UVALUE_Struct (map_In uvs (fun x _ => uvalue_convert_lazy x))) false).
          forward H.
          rewrite uvalue_convert_lazy_equation; cbn; auto.
          forward H; auto.
      + rewrite IHuv with (b:=false); auto.

    - (* Packed Structs *)
      rewrite map_In_cons in UVC.
      cbn in UVC.
      subst.
      cbn.
      destruct (DV1.is_concrete uv) eqn:HUV.
      + rewrite IHuv with (b:=true); auto.
        cbn.
        destruct (forallb DV1.is_concrete uvs) eqn:HUVS.
        * pose proof (IHuv0 (DV2.UVALUE_Packed_struct (map_In uvs (fun x _ => uvalue_convert_lazy x))) true).
          forward H.
          rewrite uvalue_convert_lazy_equation; cbn; auto.
          forward H; auto.
        * pose proof (IHuv0 (DV2.UVALUE_Packed_struct (map_In uvs (fun x _ => uvalue_convert_lazy x))) false).
          forward H.
          rewrite uvalue_convert_lazy_equation; cbn; auto.
          forward H; auto.
      + rewrite IHuv with (b:=false); auto.

    - (* Arrays *)
      rewrite map_In_cons in UVC.
      cbn in UVC.
      subst.
      cbn.
      destruct (DV1.is_concrete uv) eqn:HUV.
      + rewrite IHuv with (b:=true); auto.
        cbn.
        destruct (forallb DV1.is_concrete uvs) eqn:HUVS.
        * pose proof (IHuv0 (DV2.UVALUE_Array (map_In uvs (fun x _ => uvalue_convert_lazy x))) true).
          forward H.
          rewrite uvalue_convert_lazy_equation; cbn; auto.
          forward H; auto.
        * pose proof (IHuv0 (DV2.UVALUE_Array (map_In uvs (fun x _ => uvalue_convert_lazy x))) false).
          forward H.
          rewrite uvalue_convert_lazy_equation; cbn; auto.
          forward H; auto.
      + rewrite IHuv with (b:=false); auto.

    - (* Vectors *)
      rewrite map_In_cons in UVC.
      cbn in UVC.
      subst.
      cbn.
      destruct (DV1.is_concrete uv) eqn:HUV.
      + rewrite IHuv with (b:=true); auto.
        cbn.
        destruct (forallb DV1.is_concrete uvs) eqn:HUVS.
        * pose proof (IHuv0 (DV2.UVALUE_Vector (map_In uvs (fun x _ => uvalue_convert_lazy x))) true).
          forward H.
          rewrite uvalue_convert_lazy_equation; cbn; auto.
          forward H; auto.
        * pose proof (IHuv0 (DV2.UVALUE_Vector (map_In uvs (fun x _ => uvalue_convert_lazy x))) false).
          forward H.
          rewrite uvalue_convert_lazy_equation; cbn; auto.
          forward H; auto.
      + rewrite IHuv with (b:=false); auto.
  Qed.
 *)
  
  Lemma uvalue_refine_strict_preserves_is_concrete :
    forall uv uvc b,
      uvalue_refine_strict uv uvc ->
      DV1.is_concrete uv = b ->
      DV2.is_concrete uvc = b.
  Proof.
    induction uv using DV1.uvalue_ind';
      intros uvc b UVC CONC; cbn in *;
      rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation in UVC;
      try solve
        [ cbn in *; subst; try break_match; inv UVC; cbn; auto
        | cbn in *; subst;
          break_match_hyp; inv UVC;
          break_match_hyp; inv H0;
          eauto
        ].

    - (* Structs *)
      rewrite map_monad_InT_cons in UVC.
      cbn in UVC.
      subst.
      break_match_hyp; inv UVC.
      break_match_hyp; inv Heqo.
      break_match_hyp; inv H0.
      cbn.
      destruct (DV1.is_concrete uv) eqn:HUV.
      + rewrite IHuv with (b:=true); auto.
        cbn.
        destruct (forallb DV1.is_concrete uvs) eqn:HUVS.
        * pose proof (IHuv0 (DV2.UVALUE_Struct l0) true).
          forward H.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation.  cbn.

          rewrite Heqo; auto.
          forward H; auto.
        * pose proof (IHuv0 (DV2.UVALUE_Struct l0) false).
          forward H.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation; cbn; rewrite Heqo; auto.
          forward H; auto.
      + rewrite IHuv with (b:=false); auto.

    - (* Packed Structs *)
      rewrite map_monad_InT_cons in UVC.
      cbn in UVC.
      subst.
      break_match_hyp; inv UVC.
      break_match_hyp; inv Heqo.
      break_match_hyp; inv H0.
      cbn.
      destruct (DV1.is_concrete uv) eqn:HUV.
      + rewrite IHuv with (b:=true); auto.
        cbn.
        destruct (forallb DV1.is_concrete uvs) eqn:HUVS.
        * pose proof (IHuv0 (DV2.UVALUE_Packed_struct l0) true).
          forward H.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation; cbn; rewrite Heqo; auto.
          forward H; auto.
        * pose proof (IHuv0 (DV2.UVALUE_Packed_struct l0) false).
          forward H.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation; cbn; rewrite Heqo; auto.
          forward H; auto.
      + rewrite IHuv with (b:=false); auto.

    - (* Arrays *)
      rewrite map_monad_InT_cons in UVC.
      cbn in UVC.
      subst.
      break_match_hyp; inv UVC.
      break_match_hyp; inv Heqo.
      break_match_hyp; inv H0.
      cbn.
      destruct (DV1.is_concrete uv) eqn:HUV.
      + rewrite IHuv with (b:=true); auto.
        cbn.
        destruct (forallb DV1.is_concrete uvs) eqn:HUVS.
        * pose proof (IHuv0 (DV2.UVALUE_Array l0) true).
          forward H.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation; cbn; rewrite Heqo; auto.
          forward H; auto.
        * pose proof (IHuv0 (DV2.UVALUE_Array l0) false).
          forward H.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation; cbn; rewrite Heqo; auto.
          forward H; auto.
      + rewrite IHuv with (b:=false); auto.

    - (* Vectors *)
      rewrite map_monad_InT_cons in UVC.
      cbn in UVC.
      subst.
      break_match_hyp; inv UVC.
      break_match_hyp; inv Heqo.
      break_match_hyp; inv H0.
      cbn.
      destruct (DV1.is_concrete uv) eqn:HUV.
      + rewrite IHuv with (b:=true); auto.
        cbn.
        destruct (forallb DV1.is_concrete uvs) eqn:HUVS.
        * pose proof (IHuv0 (DV2.UVALUE_Vector l0) true).
          forward H.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation; cbn; rewrite Heqo; auto.
          forward H; auto.
        * pose proof (IHuv0 (DV2.UVALUE_Vector l0) false).
          forward H.
          rewrite uvalue_refine_strict_equation, uvalue_convert_strict_equation; cbn; rewrite Heqo; auto.
          forward H; auto.
      + rewrite IHuv with (b:=false); auto.
    - (* GEP *)
      cbn in *.
      break_match_hyp; inv UVC.
      break_match_hyp; inv H1.
      eauto.
    - cbn in *.
      break_match_hyp; inv UVC.
      break_match_hyp; inv H0.
      break_match_hyp; inv H1.
      eauto.
    - cbn in *.
      break_match_hyp; inv UVC.
      break_match_hyp; inv H0.
      break_match_hyp; inv H1.
      eauto.
    - cbn in *.
      break_match_hyp; inv UVC.
      break_match_hyp; inv H0.
      break_match_hyp; inv H1.
      eauto.
  Qed.

  (** Lemmas about uvalue_to_dvalue *)

  Lemma uvalue_to_dvalue_dvalue_refine_strict :
    forall uv1 uv2 dv1,
      uvalue_refine_strict uv1 uv2 ->
      DV1.uvalue_to_dvalue uv1 = inr dv1 ->
      exists dv2, DV2.uvalue_to_dvalue uv2 = inr dv2 /\
               dvalue_refine_strict dv1 dv2.
  Proof.
    induction uv1 using DV1.uvalue_ind';
      intros uv2 dv1 CONV UV1;
      try solve
        [ unfold_uvalue_refine_strict;
          cbn in CONV;
          (try first [break_match_hyp; inv CONV
                     | inv CONV];
           try solve
             [ cbn in *;
               inv UV1;
               try (break_match_hyp; inv CONV);
               eexists; cbn; split; eauto;
               unfold_dvalue_refine_strict; cbn; try rewrite Heqo; auto
        ])].
    - (* Structures *)
      unfold_uvalue_refine_strict.
      rewrite map_monad_InT_cons in CONV.
      cbn in CONV.

      cbn in UV1.
      break_match_hyp; inv UV1.
      break_match_hyp; inv Heqs.
      break_match_hyp; inv H0.

      break_match_hyp; inv CONV.
      break_match_hyp; inv Heqo.
      break_match_hyp; inv H0.
      rename Heqo into CONV.

      rename l0 into dvs.
      rename d into dv.

      pose proof IHuv1 as IHuv1'.
      pose proof IHuv0 as IHuv0'.
      move IHuv1' at top.
      move IHuv0' at top.

      cbn in *.
      rewrite Heqs in IHuv0.


      specialize (IHuv0 (DV2.UVALUE_Struct l1) (DV1.DVALUE_Struct dvs)).
      forward IHuv0.
      { unfold_uvalue_refine_strict.
        cbn. rewrite CONV.
        reflexivity.
      }
      specialize (IHuv0 eq_refl).
      destruct IHuv0 as [dv2 [IH DV2REF]].
      specialize (IHuv1 u dv).
      forward IHuv1. auto.
      forward IHuv1. reflexivity.
      destruct IHuv1 as [dc [DC DCREF]].

      cbn in IH.
      break_match_hyp; inv IH.
      rename l into dvs2.

      exists (DV2.DVALUE_Struct (dc :: dvs2)).

      split.
      { cbn.
        rewrite DC.
        reflexivity.
      }

      { unfold_dvalue_refine_strict_in DV2REF.
        cbn in DV2REF.
        break_match_hyp; inv DV2REF.
        unfold_dvalue_refine_strict_goal.
        rewrite map_monad_InT_cons.
        cbn.
        rewrite DCREF.
        rewrite Heqo.
        reflexivity.
      }
    - (* Packed structures *)
      unfold_uvalue_refine_strict.
      rewrite map_monad_InT_cons in CONV.
      cbn in CONV.

      cbn in UV1.
      break_match_hyp; inv UV1.
      break_match_hyp; inv Heqs.
      break_match_hyp; inv H0.

      break_match_hyp; inv CONV.
      break_match_hyp; inv Heqo.
      break_match_hyp; inv H0.
      rename Heqo into CONV.

      rename l0 into dvs.
      rename d into dv.

      pose proof IHuv1 as IHuv1'.
      pose proof IHuv0 as IHuv0'.
      move IHuv1' at top.
      move IHuv0' at top.

      cbn in *.
      rewrite Heqs in IHuv0.


      specialize (IHuv0 (DV2.UVALUE_Packed_struct l1) (DV1.DVALUE_Packed_struct dvs)).
      forward IHuv0.
      { unfold_uvalue_refine_strict.
        cbn. rewrite CONV.
        reflexivity.
      }
      specialize (IHuv0 eq_refl).
      destruct IHuv0 as [dv2 [IH DV2REF]].
      specialize (IHuv1 u dv).
      forward IHuv1. auto.
      forward IHuv1. reflexivity.
      destruct IHuv1 as [dc [DC DCREF]].

      cbn in IH.
      break_match_hyp; inv IH.
      rename l into dvs2.

      exists (DV2.DVALUE_Packed_struct (dc :: dvs2)).

      split.
      { cbn.
        rewrite DC.
        reflexivity.
      }

      { unfold_dvalue_refine_strict_in DV2REF.
        cbn in DV2REF.
        break_match_hyp; inv DV2REF.
        unfold_dvalue_refine_strict_goal.
        rewrite map_monad_InT_cons.
        cbn.
        rewrite DCREF.
        rewrite Heqo.
        reflexivity.
      }
    - (* Arrays cons *)
      cbn in *.
      break_match_hyp; inv UV1.
      break_match_hyp; inv Heqs.
      break_match_hyp; inv H0.

      unfold_uvalue_refine_strict.
      rewrite map_monad_InT_cons in CONV.
      cbn in CONV.

      break_match_hyp; inv CONV.
      break_match_hyp; inv Heqo.
      break_match_hyp; inv H0.

      specialize (IHuv1 u d).
      forward IHuv1; auto.
      specialize (IHuv1 eq_refl).
      destruct IHuv1 as [dv2 [U2Ddv2 DV2REF]].

      cbn.
      rewrite U2Ddv2.

      specialize (IHuv0 (DV2.UVALUE_Array l1) (DV1.DVALUE_Array l0)).
      forward IHuv0.
      { unfold_uvalue_refine_strict_goal.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      specialize (IHuv0 eq_refl).

      destruct IHuv0 as [dvs [U2Ddvs DVSREF]].
      cbn in *.
      break_match_hyp; inv U2Ddvs.
      eexists; split; auto.
      unfold_dvalue_refine_strict_goal.
      rewrite map_monad_InT_cons.
      cbn.
      rewrite DV2REF.
      unfold_dvalue_refine_strict_in DVSREF.
      cbn in DVSREF.
      break_match_hyp; inv DVSREF.
      auto.
    - (* Vectors cons *)
      cbn in *.
      break_match_hyp; inv UV1.
      break_match_hyp; inv Heqs.
      break_match_hyp; inv H0.

      unfold_uvalue_refine_strict.
      rewrite map_monad_InT_cons in CONV.
      cbn in CONV.

      break_match_hyp; inv CONV.
      break_match_hyp; inv Heqo.
      break_match_hyp; inv H0.

      specialize (IHuv1 u d).
      forward IHuv1; auto.
      specialize (IHuv1 eq_refl).
      destruct IHuv1 as [dv2 [U2Ddv2 DV2REF]].

      cbn.
      rewrite U2Ddv2.

      specialize (IHuv0 (DV2.UVALUE_Vector l1) (DV1.DVALUE_Vector l0)).
      forward IHuv0.
      { unfold_uvalue_refine_strict_goal.
        cbn.
        rewrite Heqo.
        reflexivity.
      }

      specialize (IHuv0 eq_refl).

      destruct IHuv0 as [dvs [U2Ddvs DVSREF]].
      cbn in *.
      break_match_hyp; inv U2Ddvs.
      eexists; split; auto.
      unfold_dvalue_refine_strict_goal.
      rewrite map_monad_InT_cons.
      cbn.
      rewrite DV2REF.
      unfold_dvalue_refine_strict_in DVSREF.
      cbn in DVSREF.
      break_match_hyp; inv DVSREF.
      auto.
  Qed.

  Lemma uvalue_to_dvalue_dvalue_refine_strict_error :
    forall uv1 uv2 s,
      uvalue_refine_strict uv1 uv2 ->
      DV1.uvalue_to_dvalue uv1 = inl s ->
      exists s', DV2.uvalue_to_dvalue uv2 = inl s'.
  Proof.
    induction uv1 using DV1.uvalue_ind';
      intros uv2 dv1 CONV UV1;
      try solve
        [ unfold_uvalue_refine_strict;
          cbn in CONV;
          (try first [break_match_hyp; inv CONV
                     | inv CONV];
           try solve
             [ cbn in *;
               inv UV1;
               try (break_match_hyp; inv CONV);
               eexists; cbn; split; eauto;
               unfold_dvalue_refine_strict; cbn; try rewrite Heqo; auto
          ])
        | unfold_uvalue_refine_strict;
          cbn in *;
          break_match_hyp; inv CONV;
          break_match_hyp; inv H0;
          cbn;
          eexists; eauto
        | cbn in *;
          unfold_uvalue_refine_strict;
          cbn in *;
          break_match_hyp; inv CONV;
          break_match_hyp; inv H1;
          cbn; eexists; eauto
        | cbn in *;
          unfold_uvalue_refine_strict;
          cbn in *;
          break_match_hyp; inv CONV;
          break_match_hyp; inv H0;
          break_match_hyp; inv H1;
          cbn; eexists; eauto
        ].
    - (* Structures *)
      unfold_uvalue_refine_strict.
      rewrite map_monad_InT_cons in CONV.
      cbn in CONV.
      cbn in UV1.
      break_match_hyp; inv UV1.
      break_match_hyp; inv Heqs.
      + break_match_hyp; inv CONV.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.
        rename Heqo into CONV.

        rename l0 into dvs.

        pose proof IHuv1 as IHuv1'.
        pose proof IHuv0 as IHuv0'.
        move IHuv1' at top.
        move IHuv0' at top.

        cbn in *.
        specialize (IHuv1 u dv1 Heqo0 eq_refl).
        destruct IHuv1.
        exists x. rewrite H.
        reflexivity.
      + break_match_hyp; inv H0.
        break_match_hyp; inv CONV.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.
        cbn.
        destruct (DV2.uvalue_to_dvalue u) eqn:HU.
        eexists; reflexivity.

        destruct (map_monad DV2.uvalue_to_dvalue l0) eqn:Hl0.
        eexists; reflexivity.

        exfalso.

        assert (uvalue_refine_strict (DV1.UVALUE_Struct uvs) (DV2.UVALUE_Struct l0)) as REFSTRUCT.
        { unfold_uvalue_refine_strict.
          cbn.
          rewrite Heqo.
          reflexivity.
        }

        epose proof IHuv0 _ _ REFSTRUCT.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        rewrite Hl0 in H.
        destruct H.
        inv H.
    - (* Packed structures *)
      unfold_uvalue_refine_strict.
      rewrite map_monad_InT_cons in CONV.
      cbn in CONV.
      cbn in UV1.
      break_match_hyp; inv UV1.
      break_match_hyp; inv Heqs.
      + break_match_hyp; inv CONV.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.
        rename Heqo into CONV.

        rename l0 into dvs.

        pose proof IHuv1 as IHuv1'.
        pose proof IHuv0 as IHuv0'.
        move IHuv1' at top.
        move IHuv0' at top.

        cbn in *.
        specialize (IHuv1 u dv1 Heqo0 eq_refl).
        destruct IHuv1.
        exists x. rewrite H.
        reflexivity.
      + break_match_hyp; inv H0.
        break_match_hyp; inv CONV.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.
        cbn.
        destruct (DV2.uvalue_to_dvalue u) eqn:HU.
        eexists; reflexivity.

        destruct (map_monad DV2.uvalue_to_dvalue l0) eqn:Hl0.
        eexists; reflexivity.

        exfalso.

        assert (uvalue_refine_strict (DV1.UVALUE_Packed_struct uvs) (DV2.UVALUE_Packed_struct l0)) as REFSTRUCT.
        { unfold_uvalue_refine_strict.
          cbn.
          rewrite Heqo.
          reflexivity.
        }

        epose proof IHuv0 _ _ REFSTRUCT.
        cbn in H.
        rewrite Heqs in H.
        forward H. reflexivity.
        rewrite Hl0 in H.
        destruct H.
        inv H.
    - (* Arrays cons *)
      cbn in *.
      break_match_hyp; inv UV1.
      break_match_hyp; inv Heqs.
      + unfold_uvalue_refine_strict.
        rewrite map_monad_InT_cons in CONV.
        cbn in *.
        break_match_hyp; inv CONV.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.

        specialize (IHuv1 _ dv1 Heqo0 eq_refl).
        cbn in *.
        destruct IHuv1 as [s' IHuv1].
        rewrite IHuv1.
        eexists; reflexivity.
      + break_match_hyp; inv H0.
        unfold_uvalue_refine_strict.
        rewrite map_monad_InT_cons in CONV.
        cbn in *.
        break_match_hyp; inv CONV.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.

        assert (uvalue_refine_strict (DV1.UVALUE_Array uvs) (DV2.UVALUE_Array l0)) as REF.
        { unfold_uvalue_refine_strict_goal.
          cbn.
          rewrite Heqo.
          reflexivity.
        }

        cbn.
        destruct (DV2.uvalue_to_dvalue u) eqn:HU.
        eexists; reflexivity.

        eapply IHuv0 in REF; eauto.
        destruct REF as [s' REF].
        exists s'.
        cbn in *.
        break_match_hyp; inv REF.
        reflexivity.
    - (* Vector cons *)
      cbn in *.
      break_match_hyp; inv UV1.
      break_match_hyp; inv Heqs.
      + unfold_uvalue_refine_strict.
        rewrite map_monad_InT_cons in CONV.
        cbn in *.
        break_match_hyp; inv CONV.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.

        specialize (IHuv1 _ dv1 Heqo0 eq_refl).
        cbn in *.
        destruct IHuv1 as [s' IHuv1].
        rewrite IHuv1.
        eexists; reflexivity.
      + break_match_hyp; inv H0.
        unfold_uvalue_refine_strict.
        rewrite map_monad_InT_cons in CONV.
        cbn in *.
        break_match_hyp; inv CONV.
        break_match_hyp; inv Heqo.
        break_match_hyp; inv H0.

        assert (uvalue_refine_strict (DV1.UVALUE_Vector uvs) (DV2.UVALUE_Vector l0)) as REF.
        { unfold_uvalue_refine_strict_goal.
          cbn.
          rewrite Heqo.
          reflexivity.
        }

        cbn.
        destruct (DV2.uvalue_to_dvalue u) eqn:HU.
        eexists; reflexivity.

        eapply IHuv0 in REF; eauto.
        destruct REF as [s' REF].
        exists s'.
        cbn in *.
        break_match_hyp; inv REF.
        reflexivity.
  Qed.

  (** Lemmas about default dvalues *)

  (* TODO: Does this one belong here? *)
  Lemma default_dvalue_of_dtyp_i_dv1_dv2_same_error :
    forall sz s,
      DV1.default_dvalue_of_dtyp_i sz = inl s <->
        DV2.default_dvalue_of_dtyp_i sz = inl s.
  Proof.
    intros sz s.
    split; intros S.
    { pose proof (@IX_supported_dec sz) as [SUPPORTED | NSUPPORTED].
      * inv SUPPORTED; cbn in *; inv S.
      * unfold DV2.default_dvalue_of_dtyp_i, DV1.default_dvalue_of_dtyp_i in *.
        assert (sz <> 1)%N by
          (intros CONTRA; subst; apply NSUPPORTED; constructor).
        assert (sz <> 8)%N by
          (intros CONTRA; subst; apply NSUPPORTED; constructor).
        assert (sz <> 32)%N by
          (intros CONTRA; subst; apply NSUPPORTED; constructor).
        assert (sz <> 64)%N by
          (intros CONTRA; subst; apply NSUPPORTED; constructor).

        apply N.eqb_neq in H, H0, H1, H2.
        rewrite H, H0, H1, H2 in S.
        rewrite H, H0, H1, H2.
        inv S. auto.
    }
    { pose proof (@IX_supported_dec sz) as [SUPPORTED | NSUPPORTED].
      * inv SUPPORTED; cbn in *; inv S.
      * unfold DV2.default_dvalue_of_dtyp_i, DV1.default_dvalue_of_dtyp_i in *.
        assert (sz <> 1)%N by
          (intros CONTRA; subst; apply NSUPPORTED; constructor).
        assert (sz <> 8)%N by
          (intros CONTRA; subst; apply NSUPPORTED; constructor).
        assert (sz <> 32)%N by
          (intros CONTRA; subst; apply NSUPPORTED; constructor).
        assert (sz <> 64)%N by
          (intros CONTRA; subst; apply NSUPPORTED; constructor).

        apply N.eqb_neq in H, H0, H1, H2.
        rewrite H, H0, H1, H2 in S.
        rewrite H, H0, H1, H2.
        inv S. auto.
    }
  Qed.

  Lemma default_dvalue_of_dtyp_i_dv1_dv2_equiv :
    forall sz v1,
      DV1.default_dvalue_of_dtyp_i sz = inr v1 ->
      exists v2,
        DV2.default_dvalue_of_dtyp_i sz = inr v2 /\ dvalue_refine_strict v1 v2.
  Proof.
    intros sz v1 V1.
    pose proof (@IX_supported_dec sz) as [SUPPORTED | NSUPPORTED].
    - inv SUPPORTED; cbn in *; inv V1;
        (eexists; split; [eauto | unfold_dvalue_refine_strict_goal; auto]).
    - unfold DV2.default_dvalue_of_dtyp_i, DV1.default_dvalue_of_dtyp_i in *.
      assert (sz <> 1)%N by
        (intros CONTRA; subst; apply NSUPPORTED; constructor).
      assert (sz <> 8)%N by
        (intros CONTRA; subst; apply NSUPPORTED; constructor).
      assert (sz <> 32)%N by
        (intros CONTRA; subst; apply NSUPPORTED; constructor).
      assert (sz <> 64)%N by
        (intros CONTRA; subst; apply NSUPPORTED; constructor).

      apply N.eqb_neq in H, H0, H1, H2.
      rewrite H, H0, H1, H2 in V1.
      inv V1.
  Qed.

  Lemma default_dvalue_of_dtyp_i_dv1_dv2_equiv' :
    forall sz v2,
      DV2.default_dvalue_of_dtyp_i sz = inr v2 ->
      exists v1,
        DV1.default_dvalue_of_dtyp_i sz = inr v1 /\ dvalue_refine_strict v1 v2.
  Proof.
    intros sz v2 V2.
    pose proof (@IX_supported_dec sz) as [SUPPORTED | NSUPPORTED].
    - inv SUPPORTED; cbn in *; inv V2;
        (eexists; split; [eauto | unfold_dvalue_refine_strict_goal; auto]).
    - unfold DV2.default_dvalue_of_dtyp_i, DV1.default_dvalue_of_dtyp_i in *.
      assert (sz <> 1)%N by
        (intros CONTRA; subst; apply NSUPPORTED; constructor).
      assert (sz <> 8)%N by
        (intros CONTRA; subst; apply NSUPPORTED; constructor).
      assert (sz <> 32)%N by
        (intros CONTRA; subst; apply NSUPPORTED; constructor).
      assert (sz <> 64)%N by
        (intros CONTRA; subst; apply NSUPPORTED; constructor).

      apply N.eqb_neq in H, H0, H1, H2.
      rewrite H, H0, H1, H2 in V2.
      inv V2.
  Qed.

  Lemma default_dvalue_of_dtyp_dv1_dv2_equiv :
    forall dt v1,
      DV1.default_dvalue_of_dtyp dt = inr v1 ->
      exists v2, DV2.default_dvalue_of_dtyp dt = inr v2 /\ dvalue_refine_strict v1 v2.
  Proof.
    induction dt; intros v1 V1;
      try solve
        [
          cbn in *; inv V1;
          eexists; split; eauto;
          unfold_dvalue_refine_strict_goal; cbn;
          auto
        ].
    - apply default_dvalue_of_dtyp_i_dv1_dv2_equiv; auto.
    - cbn in *; inv V1;
        eexists; split; eauto.
      unfold_dvalue_refine_strict_goal; cbn.
      rewrite LP1.IP.to_Z_0.
      rewrite LP2.IP.from_Z_0.
      auto.
    - cbn in *; inv V1;
        eexists; split; eauto.
      unfold_dvalue_refine_strict_goal; cbn.
      rewrite addr_convert_null.
      reflexivity.
    - (* Arrays *)
      cbn in *.
      break_match_hyp; inv V1.
      specialize (IHdt d eq_refl) as [v2 [DEFv2 REFv2]].
      eexists.
      rewrite DEFv2; split; eauto.
      unfold_dvalue_refine_strict_goal.
      cbn.
      break_match.
      2: {
        apply map_monad_InT_OOM_fail in Heqo.
        destruct Heqo as [a [IN CONVa]].
        apply repeat_spec_InT in IN; subst.
        rewrite REFv2 in CONVa.
        inv CONVa.
      }

      destruct (N.to_nat sz).
      + cbn in *.
        inv Heqo; auto.
      + apply map_monad_InT_OOM_repeat_success with (y:=v2) in Heqo; cbn; auto.
        cbn in *.
        subst.
        auto.

    - (* Structs *)
      cbn in *.
      break_match_hyp; inv V1.
      generalize dependent l.
      induction fields; intros l Heqs.
      { cbn in *; inv Heqs.
        eexists; split; eauto;
          solve_dvalue_refine_strict.
      }

      rewrite map_monad_unfold in *.
      cbn in *.

      break_match_hyp; inv Heqs.
      break_match_hyp; inv H1.

      forward IHfields; eauto.
      specialize (IHfields _ eq_refl).
      destruct IHfields as [v2 [MAPfields REFfields]].
      break_match_hyp; inv MAPfields.

      specialize (H a (or_introl eq_refl) d Heqs0) as [v2 [DEFv2 REFv2]].
      rewrite DEFv2.
      eexists; split; eauto.

      unfold_dvalue_refine_strict_goal.
      rewrite map_monad_InT_cons.
      cbn.
      rewrite REFv2.

      unfold_dvalue_refine_strict_in REFfields.
      cbn in REFfields.
      break_match_hyp; inv REFfields.
      auto.
    - (* Packed Structs *)
      cbn in *.
      break_match_hyp; inv V1.
      generalize dependent l.
      induction fields; intros l Heqs.
      { cbn in *; inv Heqs.
        eexists; split; eauto;
          solve_dvalue_refine_strict.
      }

      rewrite map_monad_unfold in *.
      cbn in *.

      break_match_hyp; inv Heqs.
      break_match_hyp; inv H1.

      forward IHfields; eauto.
      specialize (IHfields _ eq_refl).
      destruct IHfields as [v2 [MAPfields REFfields]].
      break_match_hyp; inv MAPfields.

      specialize (H a (or_introl eq_refl) d Heqs0) as [v2 [DEFv2 REFv2]].
      rewrite DEFv2.
      eexists; split; eauto.

      unfold_dvalue_refine_strict_goal.
      rewrite map_monad_InT_cons.
      cbn.
      rewrite REFv2.

      unfold_dvalue_refine_strict_in REFfields.
      cbn in REFfields.
      break_match_hyp; inv REFfields.
      auto.
    - (* Vectors *)
      cbn in *.
      break_match_hyp; inv V1.
      { break_match_hyp; inv H0.
        apply default_dvalue_of_dtyp_i_dv1_dv2_equiv in Heqs as [v2 [DEFv2 REFv2]].
        eexists; rewrite DEFv2; split; auto.
        unfold_dvalue_refine_strict_goal.
        cbn.
        break_match.
        2: {
          apply map_monad_InT_OOM_fail in Heqo.
          destruct Heqo as [a [IN CONVa]].
          apply repeat_spec_InT in IN; subst.
          rewrite REFv2 in CONVa.
          inv CONVa.
        }

        destruct (N.to_nat sz).
        + cbn in *.
          inv Heqo; auto.
        + apply map_monad_InT_OOM_repeat_success with (y:=v2) in Heqo; cbn; auto.
          cbn in *.
          subst.
          auto.
      }

      { eexists; split; eauto.
        unfold_dvalue_refine_strict_goal.
        cbn.
        break_match.
        2: {
          apply map_monad_InT_OOM_fail in Heqo.
          destruct Heqo as [a [IN CONVa]].
          apply repeat_spec_InT in IN; subst.
          rewrite dvalue_convert_strict_equation in *.
          cbn in *.
          rewrite addr_convert_null in CONVa; inv CONVa.
        }

        destruct (N.to_nat sz).
        + cbn in *.
          inv Heqo; auto.
        + apply map_monad_InT_OOM_repeat_success with (y:=DV2.DVALUE_Addr LP2.ADDR.null) in Heqo; cbn; auto.
          cbn in *.
          subst.
          auto.
          rewrite dvalue_convert_strict_equation; cbn.
          rewrite addr_convert_null. auto.
      }

      { eexists; split; eauto.
        unfold_dvalue_refine_strict_goal.
        cbn.
        break_match.
        2: {
          apply map_monad_InT_OOM_fail in Heqo.
          destruct Heqo as [a [IN CONVa]].
          apply repeat_spec_InT in IN; subst.
          rewrite dvalue_convert_strict_equation in *.
          cbn in *.
          inv CONVa.
        }

        destruct (N.to_nat sz).
        + cbn in *.
          inv Heqo; auto.
        + apply map_monad_InT_OOM_repeat_success with (y:=DV2.DVALUE_Float Floats.Float32.zero) in Heqo; cbn; auto.
          cbn in *.
          subst.
          auto.
      }

      { eexists; split; eauto.
        unfold_dvalue_refine_strict_goal.
        cbn.
        break_match.
        2: {
          apply map_monad_InT_OOM_fail in Heqo.
          destruct Heqo as [a [IN CONVa]].
          apply repeat_spec_InT in IN; subst.
          rewrite dvalue_convert_strict_equation in *.
          cbn in *.
          inv CONVa.
        }

        destruct (N.to_nat sz).
        + cbn in *.
          inv Heqo; auto.
        + apply map_monad_InT_OOM_repeat_success with (y:=DV2.DVALUE_Double (Floats.Float32.to_double Floats.Float32.zero)) in Heqo; cbn; auto.
          cbn in *.
          subst.
          auto.
      }
  Qed.

  Lemma default_dvalue_of_dtyp_dv1_dv2_equiv' :
    forall dt v2,
      DV2.default_dvalue_of_dtyp dt = inr v2 ->
      exists v1, DV1.default_dvalue_of_dtyp dt = inr v1 /\ dvalue_refine_strict v1 v2.
  Proof.
    induction dt; intros v2 V2;
      try solve
        [
          cbn in *; inv V2;
          eexists; split; eauto;
          unfold_dvalue_refine_strict_goal; cbn;
          auto
        ].
    - apply default_dvalue_of_dtyp_i_dv1_dv2_equiv'; auto.
    - cbn in *; inv V2;
        eexists; split; eauto.
      unfold_dvalue_refine_strict_goal; cbn.
      rewrite LP1.IP.to_Z_0.
      rewrite LP2.IP.from_Z_0.
      auto.
    - cbn in *; inv V2;
        eexists; split; eauto.
      unfold_dvalue_refine_strict_goal; cbn.
      rewrite addr_convert_null.
      reflexivity.
    - (* Arrays *)
      cbn in *.
      break_match_hyp; inv V2.
      specialize (IHdt d eq_refl) as [v1 [DEFv1 REFv1]].
      eexists.
      rewrite DEFv1; split; eauto.
      unfold_dvalue_refine_strict_goal.
      cbn.
      break_match.
      2: {
        apply map_monad_InT_OOM_fail in Heqo.
        destruct Heqo as [a [IN CONVa]].
        apply repeat_spec_InT in IN; subst.
        rewrite REFv1 in CONVa.
        inv CONVa.
      }

      destruct (N.to_nat sz).
      + cbn in *.
        inv Heqo; auto.
      + eapply map_monad_InT_OOM_repeat_success with (y:=d) in Heqo; cbn; auto.
        cbn in *.
        subst.
        auto.

    - (* Structs *)
      cbn in *.
      break_match_hyp; inv V2.
      generalize dependent l.
      induction fields; intros l Heqs.
      { cbn in *; inv Heqs.
        eexists; split; eauto;
          solve_dvalue_refine_strict.
      }

      rewrite map_monad_unfold in *.
      cbn in *.

      break_match_hyp; inv Heqs.
      break_match_hyp; inv H1.

      forward IHfields; eauto.
      specialize (IHfields _ eq_refl).
      destruct IHfields as [v1 [MAPfields REFfields]].
      break_match_hyp; inv MAPfields.

      specialize (H a (or_introl eq_refl) d Heqs0) as [v1 [DEFv1 REFv1]].
      rewrite DEFv1.
      eexists; split; eauto.

      unfold_dvalue_refine_strict_goal.
      rewrite map_monad_InT_cons.
      cbn.
      rewrite REFv1.

      unfold_dvalue_refine_strict_in REFfields.
      cbn in REFfields.
      break_match_hyp; inv REFfields.
      auto.
    - (* Packed Structs *)
      cbn in *.
      break_match_hyp; inv V2.
      generalize dependent l.
      induction fields; intros l Heqs.
      { cbn in *; inv Heqs.
        eexists; split; eauto;
          solve_dvalue_refine_strict.
      }

      rewrite map_monad_unfold in *.
      cbn in *.

      break_match_hyp; inv Heqs.
      break_match_hyp; inv H1.

      forward IHfields; eauto.
      specialize (IHfields _ eq_refl).
      destruct IHfields as [v1 [MAPfields REFfields]].
      break_match_hyp; inv MAPfields.

      specialize (H a (or_introl eq_refl) d Heqs0) as [v1 [DEFv1 REFv1]].
      rewrite DEFv1.
      eexists; split; eauto.

      unfold_dvalue_refine_strict_goal.
      rewrite map_monad_InT_cons.
      cbn.
      rewrite REFv1.

      unfold_dvalue_refine_strict_in REFfields.
      cbn in REFfields.
      break_match_hyp; inv REFfields.
      auto.
    - (* Vectors *)
      cbn in *.
      break_match_hyp; inv V2.
      { break_match_hyp; inv H0.
        apply default_dvalue_of_dtyp_i_dv1_dv2_equiv' in Heqs as [v1 [DEFv1 REFv1]].
        eexists; rewrite DEFv1; split; auto.
        unfold_dvalue_refine_strict_goal.
        cbn.
        break_match.
        2: {
          apply map_monad_InT_OOM_fail in Heqo.
          destruct Heqo as [a [IN CONVa]].
          apply repeat_spec_InT in IN; subst.
          rewrite REFv1 in CONVa.
          inv CONVa.
        }

        destruct (N.to_nat sz).
        + cbn in *.
          inv Heqo; auto.
        + apply map_monad_InT_OOM_repeat_success with (y:=d) in Heqo; cbn; auto.
          cbn in *.
          subst.
          auto.
      }

      { eexists; split; eauto.
        unfold_dvalue_refine_strict_goal.
        cbn.
        break_match.
        2: {
          apply map_monad_InT_OOM_fail in Heqo.
          destruct Heqo as [a [IN CONVa]].
          apply repeat_spec_InT in IN; subst.
          rewrite dvalue_convert_strict_equation in *.
          cbn in *.
          rewrite addr_convert_null in CONVa; inv CONVa.
        }

        destruct (N.to_nat sz).
        + cbn in *.
          inv Heqo; auto.
        + apply map_monad_InT_OOM_repeat_success with (y:=DV2.DVALUE_Addr LP2.ADDR.null) in Heqo; cbn; auto.
          cbn in *.
          subst.
          auto.
          rewrite dvalue_convert_strict_equation; cbn.
          rewrite addr_convert_null. auto.
      }

      { eexists; split; eauto.
        unfold_dvalue_refine_strict_goal.
        cbn.
        break_match.
        2: {
          apply map_monad_InT_OOM_fail in Heqo.
          destruct Heqo as [a [IN CONVa]].
          apply repeat_spec_InT in IN; subst.
          rewrite dvalue_convert_strict_equation in *.
          cbn in *.
          inv CONVa.
        }

        destruct (N.to_nat sz).
        + cbn in *.
          inv Heqo; auto.
        + apply map_monad_InT_OOM_repeat_success with (y:=DV2.DVALUE_Float Floats.Float32.zero) in Heqo; cbn; auto.
          cbn in *.
          subst.
          auto.
      }

      { eexists; split; eauto.
        unfold_dvalue_refine_strict_goal.
        cbn.
        break_match.
        2: {
          apply map_monad_InT_OOM_fail in Heqo.
          destruct Heqo as [a [IN CONVa]].
          apply repeat_spec_InT in IN; subst.
          rewrite dvalue_convert_strict_equation in *.
          cbn in *.
          inv CONVa.
        }

        destruct (N.to_nat sz).
        + cbn in *.
          inv Heqo; auto.
        + apply map_monad_InT_OOM_repeat_success with (y:=DV2.DVALUE_Double (Floats.Float32.to_double Floats.Float32.zero)) in Heqo; cbn; auto.
          cbn in *.
          subst.
          auto.
      }
  Qed.

  (* TODO: Move this? Seems more general... *)
  Lemma default_dvalue_of_dtyp_dv1_dv2_same_error :
    forall dt s,
      DV1.default_dvalue_of_dtyp dt = inl s <->
        DV2.default_dvalue_of_dtyp dt = inl s.
  Proof.
    intros dt s.
    split; intros S.
    { induction dt; cbn in *;
        try solve [inv S; auto].
      - apply default_dvalue_of_dtyp_i_dv1_dv2_same_error; auto.
      - rewrite IHdt; auto.
        break_match_hyp; inv S; auto.
      - (* Structs *)
        induction fields.
        + cbn in *; inv S.
        + rewrite map_monad_unfold in *.
          cbn in *.
          pose proof S.
          clear S. rename H0 into S.
          break_match_hyp; inv S.
          break_match_hyp; inv Heqs0.
          { rewrite H; auto.
          }

          break_match_hyp; inv H1.
          pose proof Heqs1.
          apply default_dvalue_of_dtyp_dv1_dv2_equiv in H0 as [v2 [DEFv2 REFv2]].
          rewrite DEFv2.

          forward IHfields; eauto.
          forward IHfields; eauto.
          break_match_hyp; inv IHfields.
          auto.
      - (* Packed Structs *)
        induction fields.
        + cbn in *; inv S.
        + rewrite map_monad_unfold in *.
          cbn in *.
          pose proof S.
          clear S. rename H0 into S.
          break_match_hyp; inv S.
          break_match_hyp; inv Heqs0.
          { rewrite H; auto.
          }

          break_match_hyp; inv H1.
          pose proof Heqs1.
          apply default_dvalue_of_dtyp_dv1_dv2_equiv in H0 as [v2 [DEFv2 REFv2]].
          rewrite DEFv2.

          forward IHfields; eauto.
          forward IHfields; eauto.
          break_match_hyp; inv IHfields.
          auto.
      - (* Vectors *)
        destruct dt; inv S; auto.
        break_match_hyp; inv H0.
        apply default_dvalue_of_dtyp_i_dv1_dv2_same_error in Heqs0.
        rewrite Heqs0.
        auto.
    }

    { induction dt; cbn in *;
        try solve [inv S; auto].
      - apply default_dvalue_of_dtyp_i_dv1_dv2_same_error; auto.
      - rewrite IHdt; auto.
        break_match_hyp; inv S; auto.
      - (* Structs *)
        induction fields.
        + cbn in *; inv S.
        + rewrite map_monad_unfold in *.
          cbn in *.
          pose proof S.
          clear S. rename H0 into S.
          break_match_hyp; inv S.
          break_match_hyp; inv Heqs0.
          { rewrite H; auto.
          }

          break_match_hyp; inv H1.
          pose proof Heqs1.
          apply default_dvalue_of_dtyp_dv1_dv2_equiv' in H0 as [v2 [DEFv2 REFv2]].
          rewrite DEFv2.

          forward IHfields; eauto.
          forward IHfields; eauto.
          break_match_hyp; inv IHfields.
          auto.
      - (* Packed Structs *)
        induction fields.
        + cbn in *; inv S.
        + rewrite map_monad_unfold in *.
          cbn in *.
          pose proof S.
          clear S. rename H0 into S.
          break_match_hyp; inv S.
          break_match_hyp; inv Heqs0.
          { rewrite H; auto.
          }

          break_match_hyp; inv H1.
          pose proof Heqs1.
          apply default_dvalue_of_dtyp_dv1_dv2_equiv' in H0 as [v2 [DEFv2 REFv2]].
          rewrite DEFv2.

          forward IHfields; eauto.
          forward IHfields; eauto.
          break_match_hyp; inv IHfields.
          auto.
      - (* Vectors *)
        destruct dt; inv S; auto.
        break_match_hyp; inv H0.
        apply default_dvalue_of_dtyp_i_dv1_dv2_same_error in Heqs0.
        rewrite Heqs0.
        auto.
    }
  Qed.

  (*
  Lemma dvalue_converted_lazy_R2_deterministic :
    R2_deterministic dvalue_converted_lazy.
  Proof.
    red.
    intros r1 r2 a b R1R2 AB.
    unfold dvalue_converted_lazy in *.
    intros EQ; subst; auto.
  Qed.
 *)

  Lemma dvalue_refine_strict_R2_injective :
    R2_injective dvalue_refine_strict.
  Proof.
    red.
    intros r1 r2 a b R1R2 AB.
    split; intros EQ; subst.
    - unfold_dvalue_refine_strict.
      rewrite R1R2 in AB. inv AB.
      auto.
    - generalize dependent r2.
      generalize dependent a.
      induction r1; intros a'; induction a'; intros r2 R1R2 AB;
        try
          solve
          [ unfold_dvalue_refine_strict;
            cbn in *;
            break_match_hyp; inv AB;
            break_match_hyp; inv R1R2;
            pose proof (addr_convert_injective _ _ _ Heqo0 Heqo);
            subst; auto
          | unfold_dvalue_refine_strict;
            cbn in *;
            break_match_hyp; inv R1R2;
            inv AB
          | unfold_dvalue_refine_strict;
            cbn in *;
            inv AB; inv R1R2; auto
          | unfold_dvalue_refine_strict;
            cbn in *;
            break_match_hyp; inv AB;
            break_match_hyp; inv R1R2;
            apply LP2.IP.from_Z_to_Z in Heqo, Heqo0;
            rewrite Heqo in Heqo0;
            apply LP1.IP.to_Z_inj in Heqo0;
            subst;
            auto
          | unfold_dvalue_refine_strict;
            cbn in R1R2;
            break_match_hyp; inv R1R2;
            inv AB
          | unfold_dvalue_refine_strict;
            cbn in *;
            break_match_hyp; inv AB;
            break_match_hyp; inv R1R2
          ].

      { (* Structs *)
        unfold_dvalue_refine_strict_in R1R2.
        unfold_dvalue_refine_strict_in AB.
        cbn in *;
          break_match_hyp; inv AB;
          break_match_hyp; inv R1R2.

        clear H0.
        generalize dependent l.
        generalize dependent fields0.
        induction fields; intros fields0 l Heqo0 Heqo.
        { clear H.
          cbn in *.
          inv Heqo0.
          apply map_monad_InT_OOM_nil_inv in Heqo; subst.
          reflexivity.
        }

        { rewrite map_monad_InT_cons in Heqo0.
          cbn in Heqo0.
          break_match_hyp; inv Heqo0.
          break_match_hyp; inv H1.

          apply map_monad_InT_OOM_cons_inv in Heqo as [x [xs [HInx [FIELDS0 [CONVX CONVXS]]]]].
          subst.

          forward IHfields.
          { intros u H1 a0 r2 R1R2 AB.
            eapply H.
            right; auto.
            eauto.
            eauto.
          }

          specialize (IHfields xs l0 eq_refl CONVXS).
          inv IHfields.

          specialize (H a (or_introl eq_refl) x d Heqo1 CONVX).
          subst.
          auto.
        }
      }

      { (* Packed Structs *)
        unfold_dvalue_refine_strict_in R1R2.
        unfold_dvalue_refine_strict_in AB.
        cbn in *;
          break_match_hyp; inv AB;
          break_match_hyp; inv R1R2.

        clear H0.
        generalize dependent l.
        generalize dependent fields0.
        induction fields; intros fields0 l Heqo0 Heqo.
        { clear H.
          cbn in *.
          inv Heqo0.

          apply map_monad_InT_OOM_nil_inv in Heqo; subst.
          reflexivity.
        }

        { rewrite map_monad_InT_cons in Heqo0.
          cbn in Heqo0.
          break_match_hyp; inv Heqo0.
          break_match_hyp; inv H1.

          apply map_monad_InT_OOM_cons_inv in Heqo as [x [xs [HInx [FIELDS0 [CONVX CONVXS]]]]].
          subst.

          forward IHfields.
          { intros u H1 a0 r2 R1R2 AB.
            eapply H.
            right; auto.
            eauto.
            eauto.
          }

          specialize (IHfields xs l0 eq_refl CONVXS).
          inv IHfields.

          specialize (H a (or_introl eq_refl) x d Heqo1 CONVX).
          subst.
          auto.
        }
      }

      { (* Arrays *)
        unfold_dvalue_refine_strict_in R1R2.
        unfold_dvalue_refine_strict_in AB.
        cbn in *;
          break_match_hyp; inv AB;
          break_match_hyp; inv R1R2.

        clear H0.
        generalize dependent l.
        generalize dependent elts0.
        induction elts; intros elts0 l Heqo0 Heqo.
        { clear H.
          cbn in *.
          inv Heqo0.

          apply map_monad_InT_OOM_nil_inv in Heqo; subst.
          reflexivity.
        }

        { rewrite map_monad_InT_cons in Heqo0.
          cbn in Heqo0.
          break_match_hyp; inv Heqo0.
          break_match_hyp; inv H1.

          apply map_monad_InT_OOM_cons_inv in Heqo as [x [xs [HInx [FIELDS0 [CONVX CONVXS]]]]].
          subst.

          forward IHelts.
          { intros u H1 a0 r2 R1R2 AB.
            eapply H.
            right; auto.
            eauto.
            eauto.
          }

          specialize (IHelts xs l0 eq_refl CONVXS).
          inv IHelts.

          specialize (H a (or_introl eq_refl) x d Heqo1 CONVX).
          subst.
          auto.
        }
      }

      { (* Vectors *)
        unfold_dvalue_refine_strict_in R1R2.
        unfold_dvalue_refine_strict_in AB.
        cbn in *;
          break_match_hyp; inv AB;
          break_match_hyp; inv R1R2.

        clear H0.
        generalize dependent l.
        generalize dependent elts0.
        induction elts; intros elts0 l Heqo0 Heqo.
        { clear H.
          cbn in *.
          inv Heqo0.

          apply map_monad_InT_OOM_nil_inv in Heqo; subst.
          reflexivity.
        }

        { rewrite map_monad_InT_cons in Heqo0.
          cbn in Heqo0.
          break_match_hyp; inv Heqo0.
          break_match_hyp; inv H1.

          apply map_monad_InT_OOM_cons_inv in Heqo as [x [xs [HInx [FIELDS0 [CONVX CONVXS]]]]].
          subst.

          forward IHelts.
          { intros u H1 a0 r2 R1R2 AB.
            eapply H.
            right; auto.
            eauto.
            eauto.
          }

          specialize (IHelts xs l0 eq_refl CONVXS).
          inv IHelts.

          specialize (H a (or_introl eq_refl) x d Heqo1 CONVX).
          subst.
          auto.
        }
      }
  Qed.

  (** Lemmas about values with types... *)

  (*
  Lemma dvalue_refine_lazy_oom :
    forall dv dt,
      DV1.dvalue_has_dtyp dv dt ->
      dvalue_refine_lazy dv (DV2.DVALUE_Oom dt).
  Proof.
    intros dv dt H.
    destruct dv;
    rewrite dvalue_refine_lazy_equation; right; auto.
  Qed.

  Lemma uvalue_refine_lazy_oom :
    forall uv dt,
      DV1.uvalue_has_dtyp uv dt ->
      uvalue_refine_lazy uv (DV2.UVALUE_Oom dt).
  Proof.
    intros uv dt H.
    destruct uv;
    rewrite uvalue_refine_lazy_equation; right; auto.
  Qed.
   *)

End DVConvertMake.

Module DVCFinInf := DVConvertMake InterpreterStack64BitIntptr.LP InterpreterStackBigIntptr.LP FinToInfAddrConvert InterpreterStack64BitIntptr.LP.Events InterpreterStackBigIntptr.LP.Events.
Module DVCInfFin := DVConvertMake InterpreterStackBigIntptr.LP InterpreterStack64BitIntptr.LP InfToFinAddrConvert InterpreterStackBigIntptr.LP.Events InterpreterStack64BitIntptr.LP.Events.

Module DVConvertSafe
  (LP1 : LLVMParams) (LP2 : LLVMParams)
  (AC1 : AddrConvert LP1.ADDR LP2.ADDR) (AC2 : AddrConvert LP2.ADDR LP1.ADDR)
  (ACSafe : AddrConvertSafe LP1.ADDR LP2.ADDR AC1 AC2)
  (IPSafe : IPConvertSafe LP1.IP LP2.IP)
  (Events1 : LLVM_INTERACTIONS LP1.ADDR LP1.IP LP1.SIZEOF) (Events2 : LLVM_INTERACTIONS LP2.ADDR LP2.IP LP2.SIZEOF)
  (DVC1 : DVConvert LP1 LP2 AC1 Events1 Events2) (DVC2 : DVConvert LP2 LP1 AC2 Events2 Events1).
  Import ACSafe.
  Import IPSafe.

  Lemma dvalue_convert_strict_safe :
    forall dv_f,
      { dv_i : DVC1.DV2.dvalue &
                 ((DVC1.dvalue_convert_strict dv_f = NoOom dv_i) *
                    (DVC2.dvalue_convert_strict dv_i = NoOom dv_f))%type}.
  Proof.
    intros dv_f.
    induction dv_f;
      try solve [ rewrite DVC1.dvalue_convert_strict_equation;
                  eexists;
                  rewrite DVC2.dvalue_convert_strict_equation;
                  split; eauto ].
    - (* Addresses *)
      rewrite DVC1.dvalue_convert_strict_equation.
      pose proof (ACSafe.addr_convert_succeeds a) as [a2 ACSUC].
      cbn.
      exists (DVC1.DV2.DVALUE_Addr a2).
      rewrite ACSUC.
      rewrite DVC2.dvalue_convert_strict_equation.
      rewrite (ACSafe.addr_convert_safe a); auto.
    - (* Intptr expressions... *)
      rewrite DVC1.dvalue_convert_strict_equation.
      pose proof (intptr_convert_succeeds x) as [y IPSUC].
      cbn.
      exists (DVC1.DV2.DVALUE_IPTR y).
      rewrite IPSUC.
      rewrite DVC2.dvalue_convert_strict_equation.
      cbn.
      rewrite (IPSafe.intptr_convert_safe x); auto.
    - (* Structures *)
      induction fields.
      + (* No fields *)
        exists (DVC1.DV2.DVALUE_Struct []).
        rewrite DVC1.dvalue_convert_strict_equation.
        rewrite DVC2.dvalue_convert_strict_equation.
        cbn.
        split; auto.
      + (* Fields *)
        assert (InT a (a :: fields)) as INA by (cbn; auto).
        pose proof (X a INA) as HA.
        destruct HA as [dv_a [CONV1_a CONV2_a]].

        rewrite DVC1.dvalue_convert_strict_equation.
        rewrite map_monad_InT_unfold.
        cbn.
        rewrite CONV1_a.
        cbn.

        destruct (map_monad_InT fields (fun (x : DVC1.DV1.dvalue) (_ : InT x fields) => DVC1.dvalue_convert_strict x)) eqn:HMAPM.
        -- eexists; split; eauto.
           rewrite DVC2.dvalue_convert_strict_equation.
           rewrite map_monad_InT_unfold.
           cbn.
           rewrite CONV2_a.
           break_inner_match_goal.
           ++ assert (l0 = fields).
              { clear - X HMAPM Heqo.
                revert X HMAPM Heqo.
                revert l l0.

                induction fields; intros l l0 H HMAPM Heqo.
                cbn in HMAPM; inv HMAPM.
                cbn in Heqo; inv Heqo.
                reflexivity.

                rewrite map_monad_InT_unfold in HMAPM.
                cbn in HMAPM.
                destruct (DVC1.dvalue_convert_strict a0) eqn:Ha0; inv HMAPM.
                break_match_hyp; inv H1.
                rewrite map_monad_InT_unfold in Heqo.
                cbn in Heqo.
                break_match_hyp; inv Heqo.
                break_match_hyp; inv H1.

                pose proof (H a0).
                forward X. cbn; auto.
                destruct X.
                rewrite Ha0 in p.
                inv p.
                inv H0.
                rewrite Heqo1 in H1.
                inv H1.

                specialize (IHfields l1 l).
                forward IHfields.
                { intros e H0.
                  apply H.
                  destruct H0; subst; cbn; auto.
                }

                specialize (IHfields eq_refl Heqo).
                subst.
                auto.
              }

              subst.
              auto.
           ++ (* Should be a contradiction *)
             apply map_monad_InT_OOM_fail in Heqo.
             destruct Heqo as [dv [HIN DVOOM]].
             pose proof HIN as HIN'.
             apply InT_Nth in HIN' as [i HNTH].

             rewrite <- map_monad_map_monad_InT in HMAPM.
             pose proof (map_monad_OOM_Nth _ _ _ _ _ HMAPM HNTH) as [y [CONVy NTHy]].
             apply Nth_InT in NTHy.
             specialize (X y).
             forward X.
             { cbn.
               auto.
             }
             destruct X as [dv_i [CONVy_dvi CONVdvi_y]].
             rewrite CONVy_dvi in CONVy. inv CONVy.
             rewrite CONVdvi_y in DVOOM.
             inv DVOOM.
        -- apply map_monad_InT_OOM_failT in HMAPM.
           destruct HMAPM as [dv [HIN DVOOM]].
           specialize (X dv).
           forward X; cbn; auto.
           destruct X as [? [CONTRA ?]].
           rewrite CONTRA in DVOOM.
           inv DVOOM.
    - (* Packed structs *)
      induction fields.
      + (* No fields *)
        rewrite DVC1.dvalue_convert_strict_equation.
        cbn. eexists; split; eauto.
        rewrite DVC2.dvalue_convert_strict_equation.
        cbn.  auto.
      + (* Fields *)
        assert (InT a (a :: fields)) as INA by (cbn; auto).
        pose proof (X a INA) as HA.
        destruct HA as [dv_a [CONV1_a CONV2_a]].

        rewrite DVC1.dvalue_convert_strict_equation.
        rewrite map_monad_InT_unfold.
        cbn.
        rewrite CONV1_a.
        cbn.

        destruct (map_monad_InT fields (fun (x : DVC1.DV1.dvalue) (_ : InT x fields) => DVC1.dvalue_convert_strict x)) eqn:HMAPM.
        -- eexists; split; eauto.
           rewrite DVC2.dvalue_convert_strict_equation.
           rewrite map_monad_InT_unfold.
           cbn.
           rewrite CONV2_a.
           break_inner_match_goal.
           ++ assert (l0 = fields).
              { clear - X HMAPM Heqo.
                revert X HMAPM Heqo.
                revert l l0.

                induction fields; intros l l0 H HMAPM Heqo.
                cbn in HMAPM; inv HMAPM.
                cbn in Heqo; inv Heqo.
                reflexivity.

                rewrite map_monad_InT_unfold in HMAPM.
                cbn in HMAPM.
                destruct (DVC1.dvalue_convert_strict a0) eqn:Ha0; inv HMAPM.
                break_match_hyp; inv H1.
                rewrite map_monad_InT_unfold in Heqo.
                cbn in Heqo.
                break_match_hyp; inv Heqo.
                break_match_hyp; inv H1.

                pose proof (H a0).
                forward X. cbn; auto.
                destruct X.
                rewrite Ha0 in p.
                inv p.
                inv H0.
                rewrite Heqo1 in H1.
                inv H1.

                specialize (IHfields l1 l).
                forward IHfields.
                { intros e H0.
                  apply H.
                  destruct H0; subst; cbn; auto.
                }

                specialize (IHfields eq_refl Heqo).
                subst.
                auto.
              }

              subst.
              auto.
           ++ (* Should be a contradiction *)
             apply map_monad_InT_OOM_fail in Heqo.
             destruct Heqo as [dv [HIN DVOOM]].
             pose proof HIN as HIN'.
             apply InT_Nth in HIN' as [i HNTH].

             rewrite <- map_monad_map_monad_InT in HMAPM.
             pose proof (map_monad_OOM_Nth _ _ _ _ _ HMAPM HNTH) as [y [CONVy NTHy]].
             apply Nth_InT in NTHy.
             specialize (X y).
             forward X; cbn; auto.
             destruct X as [dv_i [CONVy_dvi CONVdvi_y]].
             rewrite CONVy_dvi in CONVy. inv CONVy.
             rewrite CONVdvi_y in DVOOM.
             inv DVOOM.
        -- apply map_monad_InT_OOM_failT in HMAPM.
           destruct HMAPM as [dv [HIN DVOOM]].
           specialize (X dv).
           forward X; cbn; auto.
           destruct X as [? [CONTRA ?]].
           rewrite CONTRA in DVOOM.
           inv DVOOM.
    - (* Arrays *)
      induction elts.
      + rewrite DVC1.dvalue_convert_strict_equation.
        cbn. eexists; split; eauto.
        rewrite DVC2.dvalue_convert_strict_equation.
        cbn. auto.
      + assert (InT a (a :: elts)) as INA by (cbn; auto).
        pose proof (X a INA) as HA.
        destruct HA as [dv_a [CONV1_a CONV2_a]].

        rewrite DVC1.dvalue_convert_strict_equation.
        rewrite map_monad_InT_unfold.
        cbn.
        rewrite CONV1_a.

        destruct (map_monad_InT elts (fun (x : DVC1.DV1.dvalue) (_ : InT x elts) => DVC1.dvalue_convert_strict x)) eqn:HMAPM.
        -- eexists; split; eauto.
           rewrite DVC2.dvalue_convert_strict_equation.
           rewrite map_monad_InT_unfold.
           cbn.
           rewrite CONV2_a.
           break_inner_match_goal.
           ++ assert (l0 = elts).
              { clear - X HMAPM Heqo.
                revert X HMAPM Heqo.
                revert l l0.

                induction elts; intros l l0 H HMAPM Heqo.
                cbn in HMAPM; inv HMAPM.
                cbn in Heqo; inv Heqo.
                reflexivity.

                rewrite map_monad_InT_unfold in HMAPM.
                cbn in HMAPM.
                destruct (DVC1.dvalue_convert_strict a0) eqn:Ha0; inv HMAPM.
                break_match_hyp; inv H1.
                rewrite map_monad_InT_unfold in Heqo.
                cbn in Heqo.
                break_match_hyp; inv Heqo.
                break_match_hyp; inv H1.

                pose proof (H a0).
                forward X. cbn; auto.
                destruct X.
                rewrite Ha0 in p.
                inv p.
                inv H0.
                rewrite Heqo1 in H1.
                inv H1.

                specialize (IHelts l1 l).
                forward IHelts.
                { intros e H0.
                  apply H.
                  destruct H0; subst; cbn; auto.
                }

                specialize (IHelts eq_refl Heqo).
                subst.
                auto.
              }

              subst.
              auto.
           ++ (* Should be a contradiction *)
             apply map_monad_InT_OOM_failT in Heqo.
             destruct Heqo as [dv [HIN DVOOM]].
             pose proof HIN as HIN'.
             apply InT_Nth in HIN' as [i HNTH].

             rewrite <- map_monad_map_monad_InT in HMAPM.
             pose proof (map_monad_OOM_Nth _ _ _ _ _ HMAPM HNTH) as [y [CONVy NTHy]].
             apply Nth_InT in NTHy.
             specialize (X y).
             forward X; cbn; auto.
             destruct X as [dv_i [CONVy_dvi CONVdvi_y]].
             rewrite CONVy_dvi in CONVy. inv CONVy.
             rewrite CONVdvi_y in DVOOM.
             inv DVOOM.
        -- apply map_monad_InT_OOM_failT in HMAPM.
           destruct HMAPM as [dv [HIN DVOOM]].
           specialize (X dv).
           forward X; cbn; auto.
           destruct X as [? [CONTRA ?]].
           rewrite CONTRA in DVOOM.
           inv DVOOM.
    - (* Vectors *)
      induction elts.
      + rewrite DVC1.dvalue_convert_strict_equation.
        cbn. eexists; split; eauto.
        rewrite DVC2.dvalue_convert_strict_equation.
        cbn. auto.
      + assert (InT a (a :: elts)) as INA by (cbn; auto).
        pose proof (X a INA) as HA.
        destruct HA as [dv_a [CONV1_a CONV2_a]].

        rewrite DVC1.dvalue_convert_strict_equation.
        rewrite map_monad_InT_unfold.
        cbn.
        rewrite CONV1_a.

        destruct (map_monad_InT elts (fun (x : DVC1.DV1.dvalue) (_ : InT x elts) => DVC1.dvalue_convert_strict x)) eqn:HMAPM.
        -- eexists; split; eauto.
           rewrite DVC2.dvalue_convert_strict_equation.
           rewrite map_monad_InT_unfold.
           cbn.
           rewrite CONV2_a.
           break_inner_match_goal.
           ++ assert (l0 = elts).
              { clear - X HMAPM Heqo.
                revert X HMAPM Heqo.
                revert l l0.

                induction elts; intros l l0 H HMAPM Heqo.
                cbn in HMAPM; inv HMAPM.
                cbn in Heqo; inv Heqo.
                reflexivity.

                rewrite map_monad_InT_unfold in HMAPM.
                cbn in HMAPM.
                destruct (DVC1.dvalue_convert_strict a0) eqn:Ha0; inv HMAPM.
                break_match_hyp; inv H1.
                rewrite map_monad_InT_unfold in Heqo.
                cbn in Heqo.
                break_match_hyp; inv Heqo.
                break_match_hyp; inv H1.

                pose proof (H a0).
                forward X. cbn; auto.
                destruct X.
                rewrite Ha0 in p.
                inv p.
                inv H0.
                rewrite Heqo1 in H1.
                inv H1.

                specialize (IHelts l1 l).
                forward IHelts.
                { intros e H0.
                  apply H.
                  destruct H0; subst; cbn; auto.
                }

                specialize (IHelts eq_refl Heqo).
                subst.
                auto.
              }

              subst.
              auto.
           ++ (* Should be a contradiction *)
             apply map_monad_InT_OOM_failT in Heqo.
             destruct Heqo as [dv [HIN DVOOM]].
             pose proof HIN as HIN'.
             apply InT_Nth in HIN' as [i HNTH].

             rewrite <- map_monad_map_monad_InT in HMAPM.
             pose proof (map_monad_OOM_Nth _ _ _ _ _ HMAPM HNTH) as [y [CONVy NTHy]].
             apply Nth_InT in NTHy.
             specialize (X y).
             forward X; cbn; auto.
             destruct X as [dv_i [CONVy_dvi CONVdvi_y]].
             rewrite CONVy_dvi in CONVy. inv CONVy.
             rewrite CONVdvi_y in DVOOM.
             inv DVOOM.
        -- apply map_monad_InT_OOM_failT in HMAPM.
           destruct HMAPM as [dv [HIN DVOOM]].
           specialize (X dv).
           forward X; cbn; auto.
           destruct X as [? [CONTRA ?]].
           rewrite CONTRA in DVOOM.
           inv DVOOM.
  Qed.

  Lemma uvalue_convert_strict_safe :
    forall uv_f,
      { uv_i : DVC1.DV2.uvalue &
                 ((DVC1.uvalue_convert_strict uv_f = NoOom uv_i) *
                    (DVC2.uvalue_convert_strict uv_i = NoOom uv_f))%type}.
  Proof.
    intros uv_f.
    induction uv_f;
      try solve
        [ rewrite DVC1.uvalue_convert_strict_equation; eexists;
          rewrite DVC2.uvalue_convert_strict_equation; split; auto
        | destruct IHuv_f1 as [uv_i1 [UVfi1 UVif1]];
          destruct IHuv_f2 as [uv_i2 [UVfi2 UVif2]];
          rewrite DVC1.uvalue_convert_strict_equation;
          rewrite UVfi1, UVfi2;
          cbn;
          eexists; split; eauto;
          rewrite DVC2.uvalue_convert_strict_equation;
          rewrite UVif1, UVif2;
          cbn; eauto
        | destruct IHuv_f1 as [uv_i1 [UVfi1 UVif1]];
          destruct IHuv_f2 as [uv_i2 [UVfi2 UVif2]];
          destruct IHuv_f3 as [uv_i3 [UVfi3 UVif3]];
          rewrite DVC1.uvalue_convert_strict_equation;
          rewrite UVfi1, UVfi2, UVfi3;
          cbn;
          eexists; split; eauto;
          rewrite DVC2.uvalue_convert_strict_equation;
            rewrite UVif1, UVif2, UVif3;
            cbn; eauto
        | destruct IHuv_f as [uv_i [UVfi UVif]];
          rewrite DVC1.uvalue_convert_strict_equation;
          rewrite UVfi;
          cbn;
          eexists; split; eauto;
          rewrite DVC2.uvalue_convert_strict_equation;
          rewrite UVif;
          cbn; eauto
        ].
    - (* Addresses *)
      cbn.
      pose proof (ACSafe.addr_convert_succeeds a) as [a2 ACSUC].
      rewrite DVC1.uvalue_convert_strict_equation.
      rewrite ACSUC.
      exists (DVC1.DV2.UVALUE_Addr a2).
      rewrite DVC2.uvalue_convert_strict_equation.
      rewrite (ACSafe.addr_convert_safe a); auto.
    - (* Intptr expressions... *)
      cbn.
      pose proof (intptr_convert_succeeds x) as [y IPSUC].
      rewrite DVC1.uvalue_convert_strict_equation.
      cbn.
      rewrite IPSUC.
      exists (DVC1.DV2.UVALUE_IPTR y).
      rewrite DVC2.uvalue_convert_strict_equation.
      cbn.
      rewrite (IPSafe.intptr_convert_safe x); auto.
    - (* Structures *)
      induction fields.
      + (* No fields *)
        exists (DVC1.DV2.UVALUE_Struct []).
        rewrite DVC1.uvalue_convert_strict_equation.
        rewrite DVC2.uvalue_convert_strict_equation.
        cbn.
        split; auto.
      + (* Fields *)
        assert (InT a (a :: fields)) as INA by (cbn; auto).
        pose proof (X a INA) as HA.
        destruct HA as [dv_a [CONV1_a CONV2_a]].

        rewrite DVC1.uvalue_convert_strict_equation.
        rewrite map_monad_InT_unfold.
        cbn.
        rewrite CONV1_a.
        cbn.

        destruct (map_monad_InT fields (fun (x : DVC1.DV1.uvalue) (_ : InT x fields) => DVC1.uvalue_convert_strict x)) eqn:HMAPM.
        -- eexists; split; eauto.
           rewrite DVC2.uvalue_convert_strict_equation.
           rewrite map_monad_InT_unfold.
           cbn.
           rewrite CONV2_a.
           break_inner_match_goal.
           ++ assert (l0 = fields).
              { clear - X HMAPM Heqo.
                revert X HMAPM Heqo.
                revert l l0.

                induction fields; intros l l0 H HMAPM Heqo.
                cbn in HMAPM; inv HMAPM.
                cbn in Heqo; inv Heqo.
                reflexivity.

                rewrite map_monad_InT_unfold in HMAPM.
                cbn in HMAPM.
                destruct (DVC1.uvalue_convert_strict a0) eqn:Ha0; inv HMAPM.
                break_match_hyp; inv H1.
                rewrite map_monad_InT_unfold in Heqo.
                cbn in Heqo.
                break_match_hyp; inv Heqo.
                break_match_hyp; inv H1.

                pose proof (H a0).
                forward X. cbn; auto.
                destruct X.
                rewrite Ha0 in p.
                inv p.
                inv H0.
                rewrite Heqo1 in H1.
                inv H1.

                specialize (IHfields l1 l).
                forward IHfields.
                { intros e H0.
                  apply H.
                  destruct H0; subst; cbn; auto.
                }

                specialize (IHfields eq_refl Heqo).
                subst.
                auto.
              }

              subst.
              auto.
           ++ (* Should be a contradiction *)
             apply map_monad_InT_OOM_fail in Heqo.
             destruct Heqo as [dv [HIN DVOOM]].
             pose proof HIN as HIN'.
             apply InT_Nth in HIN' as [i HNTH].

             rewrite <- map_monad_map_monad_InT in HMAPM.
             pose proof (map_monad_OOM_Nth _ _ _ _ _ HMAPM HNTH) as [y [CONVy NTHy]].
             apply Nth_InT in NTHy.
             specialize (X y).
             forward X; cbn; auto.
             destruct X as [dv_i [CONVy_dvi CONVdvi_y]].
             rewrite CONVy_dvi in CONVy. inv CONVy.
             rewrite CONVdvi_y in DVOOM.
             inv DVOOM.
        -- apply map_monad_InT_OOM_failT in HMAPM.
           destruct HMAPM as [dv [HIN DVOOM]].
           specialize (X dv).
           forward X; cbn; auto.
           destruct X as [? [CONTRA ?]].
           rewrite CONTRA in DVOOM.
           inv DVOOM.
    - (* Packed structs *)
      induction fields.
      + (* No fields *)
        eexists.
        rewrite DVC1.uvalue_convert_strict_equation.
        cbn. 
        split; eauto.
        rewrite DVC2.uvalue_convert_strict_equation.
        cbn. auto.
      + (* Fields *)
        assert (InT a (a :: fields)) as INA by (cbn; auto).
        pose proof (X a INA) as HA.
        destruct HA as [dv_a [CONV1_a CONV2_a]].

        rewrite DVC1.uvalue_convert_strict_equation.
        rewrite map_monad_InT_unfold.
        cbn.
        rewrite CONV1_a.
        cbn.

        destruct (map_monad_InT fields (fun (x : DVC1.DV1.uvalue) (_ : InT x fields) => DVC1.uvalue_convert_strict x)) eqn:HMAPM.
        -- eexists; split; eauto.
           rewrite DVC2.uvalue_convert_strict_equation.
           rewrite map_monad_InT_unfold.
           cbn.
           rewrite CONV2_a.
           break_inner_match_goal.
           ++ assert (l0 = fields).
              { clear - X HMAPM Heqo.
                revert X HMAPM Heqo.
                revert l l0.

                induction fields; intros l l0 H HMAPM Heqo.
                cbn in HMAPM; inv HMAPM.
                cbn in Heqo; inv Heqo.
                reflexivity.

                rewrite map_monad_InT_unfold in HMAPM.
                cbn in HMAPM.
                destruct (DVC1.uvalue_convert_strict a0) eqn:Ha0; inv HMAPM.
                break_match_hyp; inv H1.
                rewrite map_monad_InT_unfold in Heqo.
                cbn in Heqo.
                break_match_hyp; inv Heqo.
                break_match_hyp; inv H1.

                pose proof (H a0).
                forward X. cbn; auto.
                destruct X.
                rewrite Ha0 in p.
                inv p.
                inv H0.
                rewrite Heqo1 in H1.
                inv H1.

                specialize (IHfields l1 l).
                forward IHfields.
                { intros e H0.
                  apply H.
                  destruct H0; subst; cbn; auto.
                }

                specialize (IHfields eq_refl Heqo).
                subst.
                auto.
              }

              subst.
              auto.
           ++ (* Should be a contradiction *)
             apply map_monad_InT_OOM_fail in Heqo.
             destruct Heqo as [dv [HIN DVOOM]].
             pose proof HIN as HIN'.
             apply InT_Nth in HIN' as [i HNTH].

             rewrite <- map_monad_map_monad_InT in HMAPM.
             pose proof (map_monad_OOM_Nth _ _ _ _ _ HMAPM HNTH) as [y [CONVy NTHy]].
             apply Nth_InT in NTHy.
             specialize (X y).
             forward X; cbn; auto.
             destruct X as [dv_i [CONVy_dvi CONVdvi_y]].
             rewrite CONVy_dvi in CONVy. inv CONVy.
             rewrite CONVdvi_y in DVOOM.
             inv DVOOM.
        -- apply map_monad_InT_OOM_failT in HMAPM.
           destruct HMAPM as [dv [HIN DVOOM]].
           specialize (X dv).
           forward X; cbn; auto.
           destruct X as [? [CONTRA ?]].
           rewrite CONTRA in DVOOM.
           inv DVOOM.
    - (* Arrays *)
      induction elts.
      + rewrite DVC1.uvalue_convert_strict_equation.
        cbn. eexists; split; eauto.
        rewrite DVC2.uvalue_convert_strict_equation.
        reflexivity.
      + assert (InT a (a :: elts)) as INA by (cbn; auto).
        pose proof (X a INA) as HA.
        destruct HA as [dv_a [CONV1_a CONV2_a]].

        rewrite DVC1.uvalue_convert_strict_equation.
        rewrite map_monad_InT_unfold.
        cbn.
        rewrite CONV1_a.

        destruct (map_monad_InT elts (fun (x : DVC1.DV1.uvalue) (_ : InT x elts) => DVC1.uvalue_convert_strict x)) eqn:HMAPM.
        -- eexists; split; eauto.
           rewrite DVC2.uvalue_convert_strict_equation.
           rewrite map_monad_InT_unfold.
           cbn.
           rewrite CONV2_a.
           break_inner_match_goal.
           ++ assert (l0 = elts).
              { clear - X HMAPM Heqo.
                revert X HMAPM Heqo.
                revert l l0.

                induction elts; intros l l0 H HMAPM Heqo.
                cbn in HMAPM; inv HMAPM.
                cbn in Heqo; inv Heqo.
                reflexivity.

                rewrite map_monad_InT_unfold in HMAPM.
                cbn in HMAPM.
                destruct (DVC1.uvalue_convert_strict a0) eqn:Ha0; inv HMAPM.
                break_match_hyp; inv H1.
                rewrite map_monad_InT_unfold in Heqo.
                cbn in Heqo.
                break_match_hyp; inv Heqo.
                break_match_hyp; inv H1.

                pose proof (H a0).
                forward X. cbn; auto.
                destruct X.
                rewrite Ha0 in p.
                inv p.
                inv H0.
                rewrite Heqo1 in H1.
                inv H1.

                specialize (IHelts l1 l).
                forward IHelts.
                { intros e H0.
                  apply H.
                  destruct H0; subst; cbn; auto.
                }

                specialize (IHelts eq_refl Heqo).
                subst.
                auto.
              }

              subst.
              auto.
           ++ (* Should be a contradiction *)
             apply map_monad_InT_OOM_fail in Heqo.
             destruct Heqo as [dv [HIN DVOOM]].
             pose proof HIN as HIN'.
             apply InT_Nth in HIN' as [i HNTH].

             rewrite <- map_monad_map_monad_InT in HMAPM.
             pose proof (map_monad_OOM_Nth _ _ _ _ _ HMAPM HNTH) as [y [CONVy NTHy]].
             apply Nth_InT in NTHy.
             specialize (X y).
             forward X; cbn; auto.
             destruct X as [dv_i [CONVy_dvi CONVdvi_y]].
             rewrite CONVy_dvi in CONVy. inv CONVy.
             rewrite CONVdvi_y in DVOOM.
             inv DVOOM.
        -- apply map_monad_InT_OOM_failT in HMAPM.
           destruct HMAPM as [dv [HIN DVOOM]].
           specialize (X dv).
           forward X; cbn; auto.
           destruct X as [? [CONTRA ?]].
           rewrite CONTRA in DVOOM.
           inv DVOOM.
    - (* Vectors *)
      induction elts.
      + rewrite DVC1.uvalue_convert_strict_equation.
        cbn. eexists; split; eauto.
        rewrite DVC2.uvalue_convert_strict_equation.
        reflexivity.        
      + assert (InT a (a :: elts)) as INA by (cbn; auto).
        pose proof (X a INA) as HA.
        destruct HA as [dv_a [CONV1_a CONV2_a]].

        rewrite DVC1.uvalue_convert_strict_equation.
        rewrite map_monad_InT_unfold.
        cbn.
        rewrite CONV1_a.

        destruct (map_monad_InT elts (fun (x : DVC1.DV1.uvalue) (_ : InT x elts) => DVC1.uvalue_convert_strict x)) eqn:HMAPM.
        -- eexists; split; eauto.
           rewrite DVC2.uvalue_convert_strict_equation.
           rewrite map_monad_InT_unfold.
           cbn.
           rewrite CONV2_a.
           break_inner_match_goal.
           ++ assert (l0 = elts).
              { clear - X HMAPM Heqo.
                revert X HMAPM Heqo.
                revert l l0.

                induction elts; intros l l0 H HMAPM Heqo.
                cbn in HMAPM; inv HMAPM.
                cbn in Heqo; inv Heqo.
                reflexivity.

                rewrite map_monad_InT_unfold in HMAPM.
                cbn in HMAPM.
                destruct (DVC1.uvalue_convert_strict a0) eqn:Ha0; inv HMAPM.
                break_match_hyp; inv H1.
                rewrite map_monad_InT_unfold in Heqo.
                cbn in Heqo.
                break_match_hyp; inv Heqo.
                break_match_hyp; inv H1.

                pose proof (H a0).
                forward X. cbn; auto.
                destruct X.
                rewrite Ha0 in p.
                inv p.
                inv H0.
                rewrite Heqo1 in H1.
                inv H1.

                specialize (IHelts l1 l).
                forward IHelts.
                { intros e H0.
                  apply H.
                  destruct H0; subst; cbn; auto.
                }

                specialize (IHelts eq_refl Heqo).
                subst.
                auto.
              }

              subst.
              auto.
           ++ (* Should be a contradiction *)
             apply map_monad_InT_OOM_fail in Heqo.
             destruct Heqo as [dv [HIN DVOOM]].
             pose proof HIN as HIN'.
             apply InT_Nth in HIN' as [i HNTH].

             rewrite <- map_monad_map_monad_InT in HMAPM.
             pose proof (map_monad_OOM_Nth _ _ _ _ _ HMAPM HNTH) as [y [CONVy NTHy]].
             apply Nth_InT in NTHy.
             specialize (X y).
             forward X; cbn; auto.
             destruct X as [dv_i [CONVy_dvi CONVdvi_y]].
             rewrite CONVy_dvi in CONVy. inv CONVy.
             rewrite CONVdvi_y in DVOOM.
             inv DVOOM.
        -- apply map_monad_InT_OOM_failT in HMAPM.
           destruct HMAPM as [dv [HIN DVOOM]].
           specialize (X dv).
           forward X; cbn; auto.
           destruct X as [? [CONTRA ?]].
           rewrite CONTRA in DVOOM.
           inv DVOOM.
    - (* GEP *)
      destruct IHuv_f as [uv_i [UVfi UVif]].
      rewrite DVC1.uvalue_convert_strict_equation.
        rewrite UVfi.
        cbn.

        destruct (map_monad_InT idxs (fun (elt : DVC1.DV1.uvalue) (_ : InT elt idxs) => DVC1.uvalue_convert_strict elt)) eqn:HMAPM.
      + eexists; split; eauto.
        rewrite DVC2.uvalue_convert_strict_equation.
        rewrite UVif.
        cbn; eauto.

        break_match_goal.
        * assert (l0 = idxs).
          { clear - X HMAPM Heqo.
            revert X HMAPM Heqo.
            revert l l0.

            induction idxs; intros l l0 H HMAPM Heqo.
            cbn in HMAPM; inv HMAPM.
            cbn in Heqo; inv Heqo.
            reflexivity.

            rewrite map_monad_InT_unfold in HMAPM.
            cbn in HMAPM.
            destruct (DVC1.uvalue_convert_strict a) eqn:Ha0; inv HMAPM.
            break_match_hyp; inv H1.
            rewrite map_monad_InT_unfold in Heqo.
            cbn in Heqo.
            break_match_hyp; inv Heqo.
            break_match_hyp; inv H1.

            pose proof (H a).
            forward X. cbn; auto.
            destruct X.
            rewrite Ha0 in p.
            inv p.
            inv H0.
            rewrite Heqo1 in H1.
            inv H1.

            specialize (IHidxs l1 l).
            forward IHidxs.
            { intros e H0.
              apply H.
              right; auto.
            }

            specialize (IHidxs eq_refl Heqo).
            subst.
            auto.
          }

          subst.
          auto.
        * exfalso.
          apply map_monad_InT_OOM_fail in Heqo.
          destruct Heqo as [dv [HIN DVOOM]].
          pose proof HIN as HIN'.
          apply InT_Nth in HIN' as [i HNTH].

          rewrite <- map_monad_map_monad_InT in HMAPM.
          pose proof (map_monad_OOM_Nth _ _ _ _ _ HMAPM HNTH) as [y [CONVy NTHy]].
          apply Nth_InT in NTHy.
          specialize (X y).
          forward X; cbn; auto.
          destruct X as [dv_i [CONVy_dvi CONVdvi_y]].
          rewrite CONVy_dvi in CONVy. inv CONVy.
          rewrite CONVdvi_y in DVOOM.
          inv DVOOM.
      + apply map_monad_InT_OOM_failT in HMAPM.
        destruct HMAPM as [dv [HIN DVOOM]].
        specialize (X dv).
        forward X; cbn; auto.
        destruct X as [? [CONTRA ?]].
        rewrite CONTRA in DVOOM.
        inv DVOOM.
    - (* ConcatBytes *)
      rewrite DVC1.uvalue_convert_strict_equation.
      cbn.

      destruct (map_monad_InT uvs (fun (elt : DVC1.DV1.uvalue) (_ : InT elt uvs) => DVC1.uvalue_convert_strict elt)) eqn:HMAPM.
      + eexists; split; eauto.
        rewrite DVC2.uvalue_convert_strict_equation.
        cbn.

        break_match_goal.
        * assert (l0 = uvs).
          { clear - X HMAPM Heqo.
            revert X HMAPM Heqo.
            revert l l0.

            induction uvs; intros l l0 H HMAPM Heqo.
            cbn in HMAPM; inv HMAPM.
            cbn in Heqo; inv Heqo.
            reflexivity.

            rewrite map_monad_InT_unfold in HMAPM.
            cbn in HMAPM.
            destruct (DVC1.uvalue_convert_strict a) eqn:Ha0; inv HMAPM.
            break_match_hyp; inv H1.
            rewrite map_monad_InT_unfold in Heqo.
            cbn in Heqo.
            break_match_hyp; inv Heqo.
            break_match_hyp; inv H1.

            pose proof (H a).
            forward X. cbn; auto.
            destruct X.
            rewrite Ha0 in p.
            inv p.
            inv H0.
            rewrite Heqo1 in H1.
            inv H1.

            specialize (IHuvs l1 l).
            forward IHuvs.
            { intros e H0.
              apply H.
              right; auto.
            }

            specialize (IHuvs eq_refl Heqo).
            subst.
            auto.
          }

          subst.
          auto.
        * exfalso.
          apply map_monad_InT_OOM_fail in Heqo.
          destruct Heqo as [dv [HIN DVOOM]].
          pose proof HIN as HIN'.
          apply InT_Nth in HIN' as [i HNTH].

          rewrite <- map_monad_map_monad_InT in HMAPM.
          pose proof (map_monad_OOM_Nth _ _ _ _ _ HMAPM HNTH) as [y [CONVy NTHy]].
          apply Nth_InT in NTHy.
          specialize (X y).
          forward X; cbn; auto.
          destruct X as [dv_i [CONVy_dvi CONVdvi_y]].
          rewrite CONVy_dvi in CONVy. inv CONVy.
          rewrite CONVdvi_y in DVOOM.
          inv DVOOM.
      + apply map_monad_InT_OOM_failT in HMAPM.
        destruct HMAPM as [dv [HIN DVOOM]].
        specialize (X dv).
        forward X; cbn; auto.
        destruct X as [? [CONTRA ?]].
        rewrite CONTRA in DVOOM.
        inv DVOOM.
  Qed.
End DVConvertSafe.
