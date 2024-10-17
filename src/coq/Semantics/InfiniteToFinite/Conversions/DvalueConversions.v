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
     Utils.Util
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


Module Type DVConvert (LP1 : LLVMParams) (LP2 : LLVMParams) (AC : AddrConvert LP1.ADDR LP1.PTOI LP2.ADDR LP2.PTOI) (Events1 : LLVM_INTERACTIONS LP1.ADDR LP1.IP LP1.SIZEOF) (Events2 : LLVM_INTERACTIONS LP2.ADDR LP2.IP LP2.SIZEOF).
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

    Fixpoint dvalue_convert_strict (dv1 : DV1.dvalue) : OOM DV2.dvalue
    := match dv1 with
       | DV1.DVALUE_Addr a =>
           a' <- addr_convert a;;
           ret (DV2.DVALUE_Addr a')
       | @DV1.DVALUE_I sz x  => ret (@DV2.DVALUE_I sz x)
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
           fields' <- map_monad dvalue_convert_strict fields;;
           ret (DV2.DVALUE_Struct fields')
       | DV1.DVALUE_Packed_struct fields =>
           fields' <- map_monad dvalue_convert_strict fields;;
           ret (DV2.DVALUE_Packed_struct fields')
       | DV1.DVALUE_Array t elts =>
           elts' <- map_monad dvalue_convert_strict elts;;
           ret (DV2.DVALUE_Array t elts')
       | DV1.DVALUE_Vector t elts =>
           elts' <- map_monad dvalue_convert_strict elts;;
           ret (DV2.DVALUE_Vector t elts')
       end.


  Fixpoint uvalue_convert_strict (uv1 : DV1.uvalue) : OOM DV2.uvalue
    := match uv1 with
       | DV1.UVALUE_Addr a =>
           a' <- addr_convert a;;
           ret (DV2.UVALUE_Addr a')
       | @DV1.UVALUE_I sz x  => ret (@DV2.UVALUE_I sz x)
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
           fields' <- map_monad uvalue_convert_strict fields;;
           ret (DV2.UVALUE_Struct fields')
       | DV1.UVALUE_Packed_struct fields =>
           fields' <- map_monad uvalue_convert_strict fields;;
           ret (DV2.UVALUE_Packed_struct fields')
       | DV1.UVALUE_Array t elts =>
           elts' <- map_monad uvalue_convert_strict elts;;
           ret (DV2.UVALUE_Array t elts')
       | DV1.UVALUE_Vector t elts =>
           elts' <- map_monad uvalue_convert_strict elts;;
           ret (DV2.UVALUE_Vector t elts')
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
           idxs' <- map_monad uvalue_convert_strict idxs;;
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
       | DV1.UVALUE_ShuffleVector dt vec1 vec2 idxmask =>
           vec1' <- uvalue_convert_strict vec1;;
           vec2' <- uvalue_convert_strict vec2;;
           idxmask' <- uvalue_convert_strict idxmask;;
           ret (DV2.UVALUE_ShuffleVector dt vec1' vec2' idxmask')
       | DV1.UVALUE_ExtractValue t vec idxs =>
           vec' <- uvalue_convert_strict vec;;
           ret (DV2.UVALUE_ExtractValue t vec' idxs)
       | DV1.UVALUE_InsertValue t vec et elt idxs =>
           vec' <- uvalue_convert_strict vec;;
           elt' <- uvalue_convert_strict elt;;
           ret (DV2.UVALUE_InsertValue t vec' et elt' idxs)
       | DV1.UVALUE_Select cnd v1 v2 =>
           cnd' <- uvalue_convert_strict cnd;;
           v1' <- uvalue_convert_strict v1;;
           v2' <- uvalue_convert_strict v2;;
           ret (DV2.UVALUE_Select cnd' v1' v2')
       | DV1.UVALUE_ExtractByte uv dt idx sid =>
           uv' <- uvalue_convert_strict uv;;
           ret (DV2.UVALUE_ExtractByte uv' dt idx sid)
       | DV1.UVALUE_ConcatBytes uvs dt =>
           uvs' <- map_monad uvalue_convert_strict uvs;;
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

  Ltac solve_uvalue_refine_strict :=
    solve [unfold uvalue_refine_strict;
           cbn;
           solve [ auto
                 | rewrite addr_convert_null;
                   reflexivity
             ]
      ].

  Ltac solve_dvalue_refine_strict :=
    solve [unfold dvalue_refine_strict;
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

  Parameter default_dvalue_of_dtyp_i_dv1_dv2_equiv :
    forall sz v1,
      DV1.default_dvalue_of_dtyp_i sz = v1 ->
      exists v2,
        DV2.default_dvalue_of_dtyp_i sz = v2 /\ dvalue_refine_strict v1 v2.

  Parameter default_dvalue_of_dtyp_i_dv1_dv2_equiv' :
    forall sz v2,
      DV2.default_dvalue_of_dtyp_i sz = v2 ->
      exists v1,
        DV1.default_dvalue_of_dtyp_i sz = v1 /\ dvalue_refine_strict v1 v2.

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

  Parameter uvalue_refine_strict_R2_injective :
    R2_injective uvalue_refine_strict.

  (** Dvalue Inversion Lemmas *)
  Parameter dvalue_convert_strict_addr_inv :
    forall x a,
      dvalue_convert_strict x = NoOom (DV2.DVALUE_Addr a) ->
      exists a',
        AC.addr_convert a' = NoOom a /\
          x = DV1.DVALUE_Addr a'.

  Parameter dvalue_convert_strict_iptr_inv :
    forall x n,
      dvalue_convert_strict x = NoOom (DV2.DVALUE_IPTR n) ->
      exists n',
        LP2.IP.from_Z (LP1.IP.to_Z n') = NoOom n /\
          x = DV1.DVALUE_IPTR n'.

  Parameter dvalue_convert_strict_ix_inv :
    forall sz x n,
      dvalue_convert_strict x = NoOom (@DV2.DVALUE_I sz n) ->
      x = @DV1.DVALUE_I sz n.

  Parameter dvalue_convert_strict_double_inv :
    forall x v,
      dvalue_convert_strict x = NoOom (DV2.DVALUE_Double v) ->
      x = DV1.DVALUE_Double v.

  Parameter dvalue_convert_strict_float_inv :
    forall x v,
      dvalue_convert_strict x = NoOom (DV2.DVALUE_Float v) ->
      x = DV1.DVALUE_Float v.

  Parameter dvalue_convert_strict_poison_inv :
    forall x v,
      dvalue_convert_strict x = NoOom (DV2.DVALUE_Poison v) ->
      x = DV1.DVALUE_Poison v.

  Parameter dvalue_convert_strict_oom_inv :
    forall x v,
      dvalue_convert_strict x = NoOom (DV2.DVALUE_Oom v) ->
      x = DV1.DVALUE_Oom v.

  Parameter dvalue_convert_strict_none_inv :
    forall x,
      dvalue_convert_strict x = NoOom DV2.DVALUE_None ->
      x = DV1.DVALUE_None.

  Parameter dvalue_convert_strict_struct_inv :
    forall x fields,
      dvalue_convert_strict x = NoOom (DV2.DVALUE_Struct fields) ->
      exists fields',
        x = DV1.DVALUE_Struct fields' /\
          map_monad dvalue_convert_strict fields' = NoOom fields.

  Parameter dvalue_convert_strict_packed_struct_inv :
    forall x fields,
      dvalue_convert_strict x = NoOom (DV2.DVALUE_Packed_struct fields) ->
      exists fields',
        x = DV1.DVALUE_Packed_struct fields' /\
          map_monad dvalue_convert_strict fields' = NoOom fields.

  Parameter dvalue_convert_strict_array_inv :
    forall x elts t,
      dvalue_convert_strict x = NoOom (DV2.DVALUE_Array t elts) ->
      exists elts',
        x = DV1.DVALUE_Array t elts' /\
          map_monad dvalue_convert_strict elts' = NoOom elts.

  Parameter dvalue_convert_strict_vector_inv :
    forall x elts t,
      dvalue_convert_strict x = NoOom (DV2.DVALUE_Vector t elts) ->
      exists elts',
        x = DV1.DVALUE_Vector t elts' /\
          map_monad dvalue_convert_strict elts' = NoOom elts.

  Ltac dvalue_convert_strict_inv H :=
    first
      [ apply dvalue_convert_strict_ix_inv in H
      | apply dvalue_convert_strict_iptr_inv in H
      | apply dvalue_convert_strict_addr_inv in H
      | apply dvalue_convert_strict_double_inv in H
      | apply dvalue_convert_strict_float_inv in H
      | apply dvalue_convert_strict_poison_inv in H
      | apply dvalue_convert_strict_oom_inv in H
      | apply dvalue_convert_strict_none_inv in H
      | apply dvalue_convert_strict_struct_inv in H
      | apply dvalue_convert_strict_packed_struct_inv in H
      | apply dvalue_convert_strict_array_inv in H
      | apply dvalue_convert_strict_vector_inv in H
      ];
    try first [destruct H as (?&?&?)
          | destruct H as (?&?)]; subst.

  Ltac dvalue_refine_strict_inv H :=
    rewrite dvalue_refine_strict_equation in H;
    dvalue_convert_strict_inv H.

  (** Uvalue Inversion Lemmas *)
  Parameter uvalue_convert_strict_addr_inv :
    forall x a,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_Addr a) ->
      exists a',
        AC.addr_convert a' = NoOom a /\
          x = DV1.UVALUE_Addr a'.

  Parameter uvalue_convert_strict_iptr_inv :
    forall x n,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_IPTR n) ->
      exists n',
        LP2.IP.from_Z (LP1.IP.to_Z n') = NoOom n /\
          x = DV1.UVALUE_IPTR n'.

  Parameter uvalue_convert_strict_ix_inv :
    forall sz x n,
      uvalue_convert_strict x = NoOom (@DV2.UVALUE_I sz n) ->
      x = @DV1.UVALUE_I sz n.

  Parameter uvalue_convert_strict_double_inv :
    forall x v,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_Double v) ->
      x = DV1.UVALUE_Double v.

  Parameter uvalue_convert_strict_float_inv :
    forall x v,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_Float v) ->
      x = DV1.UVALUE_Float v.

  Parameter uvalue_convert_strict_undef_inv :
    forall x v,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_Undef v) ->
      x = DV1.UVALUE_Undef v.

  Parameter uvalue_convert_strict_poison_inv :
    forall x v,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_Poison v) ->
      x = DV1.UVALUE_Poison v.

  Parameter uvalue_convert_strict_oom_inv :
    forall x v,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_Oom v) ->
      x = DV1.UVALUE_Oom v.

  Parameter uvalue_convert_strict_none_inv :
    forall x,
      uvalue_convert_strict x = NoOom DV2.UVALUE_None ->
      x = DV1.UVALUE_None.

  Parameter uvalue_convert_strict_struct_inv :
    forall x fields,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_Struct fields) ->
      exists fields',
        x = DV1.UVALUE_Struct fields' /\
          map_monad uvalue_convert_strict fields' = NoOom fields.

  Parameter uvalue_convert_strict_packed_struct_inv :
    forall x fields,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_Packed_struct fields) ->
      exists fields',
        x = DV1.UVALUE_Packed_struct fields' /\
          map_monad uvalue_convert_strict fields' = NoOom fields.

  Parameter uvalue_convert_strict_array_inv :
    forall x elts t,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_Array t elts) ->
      exists elts',
        x = DV1.UVALUE_Array t elts' /\
          map_monad uvalue_convert_strict elts' = NoOom elts.

  Parameter uvalue_convert_strict_vector_inv :
    forall x elts t,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_Vector t elts) ->
      exists elts',
        x = DV1.UVALUE_Vector t elts' /\
          map_monad uvalue_convert_strict elts' = NoOom elts.

  Parameter uvalue_convert_strict_ibinop_inv :
    forall x iop uv1 uv2,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_IBinop iop uv1 uv2) ->
      exists uv1' uv2',
        x = DV1.UVALUE_IBinop iop uv1' uv2' /\
          uvalue_convert_strict uv1' = NoOom uv1 /\
          uvalue_convert_strict uv2' = NoOom uv2.

  Parameter uvalue_convert_strict_icmp_inv :
    forall x icmp uv1 uv2,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_ICmp icmp uv1 uv2) ->
      exists uv1' uv2',
        x = DV1.UVALUE_ICmp icmp uv1' uv2' /\
          uvalue_convert_strict uv1' = NoOom uv1 /\
          uvalue_convert_strict uv2' = NoOom uv2.

  Parameter uvalue_convert_strict_fbinop_inv :
    forall x fop flags uv1 uv2,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_FBinop fop flags uv1 uv2) ->
      exists uv1' uv2',
        x = DV1.UVALUE_FBinop fop flags uv1' uv2' /\
          uvalue_convert_strict uv1' = NoOom uv1 /\
          uvalue_convert_strict uv2' = NoOom uv2.

  Parameter uvalue_convert_strict_fcmp_inv :
    forall x fcmp uv1 uv2,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_FCmp fcmp uv1 uv2) ->
      exists uv1' uv2',
        x = DV1.UVALUE_FCmp fcmp uv1' uv2' /\
          uvalue_convert_strict uv1' = NoOom uv1 /\
          uvalue_convert_strict uv2' = NoOom uv2.

  Parameter uvalue_convert_strict_conversion_inv :
    forall x conv_type dt_from uv dt_to,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_Conversion conv_type dt_from uv dt_to) ->
      exists uv',
        x = DV1.UVALUE_Conversion conv_type dt_from uv' dt_to /\
          uvalue_convert_strict uv' = NoOom uv.

  Parameter uvalue_convert_strict_gep_inv :
    forall x dt uv_addr uv_idxs,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_GetElementPtr dt uv_addr uv_idxs) ->
      exists uv_addr' uv_idxs',
        x = DV1.UVALUE_GetElementPtr dt uv_addr' uv_idxs' /\
          uvalue_convert_strict uv_addr' = NoOom uv_addr /\
          map_monad uvalue_convert_strict uv_idxs' = NoOom uv_idxs.

  Parameter uvalue_convert_strict_extract_element_inv :
    forall x dt uv uv_idx,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_ExtractElement dt uv uv_idx) ->
      exists uv' uv_idx',
        x = DV1.UVALUE_ExtractElement dt uv' uv_idx' /\
          uvalue_convert_strict uv' = NoOom uv /\
          uvalue_convert_strict uv_idx' = NoOom uv_idx.

  Parameter uvalue_convert_strict_insert_element_inv :
    forall x dt uv_vec uv_elt uv_idx,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_InsertElement dt uv_vec uv_elt uv_idx) ->
      exists uv_vec' uv_elt' uv_idx',
        x = DV1.UVALUE_InsertElement dt uv_vec' uv_elt' uv_idx' /\
          uvalue_convert_strict uv_vec' = NoOom uv_vec /\
          uvalue_convert_strict uv_elt' = NoOom uv_elt /\
          uvalue_convert_strict uv_idx' = NoOom uv_idx.

  Parameter uvalue_convert_strict_shuffle_vector_inv :
    forall x dt vec1 vec2 idxmask,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_ShuffleVector dt vec1 vec2 idxmask) ->
      exists vec1' vec2' idxmask',
        x = DV1.UVALUE_ShuffleVector dt vec1' vec2' idxmask' /\
          uvalue_convert_strict vec1' = NoOom vec1 /\
          uvalue_convert_strict vec2' = NoOom vec2 /\
          uvalue_convert_strict idxmask' = NoOom idxmask.

  Parameter uvalue_convert_strict_extract_value_inv :
    forall x dt uv idxs,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_ExtractValue dt uv idxs) ->
      exists uv',
        x = DV1.UVALUE_ExtractValue dt uv' idxs /\
          uvalue_convert_strict uv' = NoOom uv.

  Parameter uvalue_convert_strict_insert_value_inv :
    forall x dt uv dt_elt elt idxs,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_InsertValue dt uv dt_elt elt idxs) ->
      exists uv' elt',
        x = DV1.UVALUE_InsertValue dt uv' dt_elt elt' idxs /\
          uvalue_convert_strict uv' = NoOom uv /\
          uvalue_convert_strict elt' = NoOom elt.

  Parameter uvalue_convert_strict_select_inv :
    forall x cnd uv1 uv2,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_Select cnd uv1 uv2) ->
      exists cnd' uv1' uv2',
        x = DV1.UVALUE_Select cnd' uv1' uv2' /\
          uvalue_convert_strict cnd' = NoOom cnd /\
          uvalue_convert_strict uv1' = NoOom uv1 /\
          uvalue_convert_strict uv2' = NoOom uv2.

  Parameter uvalue_convert_strict_extract_byte_inv :
    forall x uv dt idx sid,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_ExtractByte uv dt idx sid) ->
      exists uv',
        x = DV1.UVALUE_ExtractByte uv' dt idx sid /\
          uvalue_convert_strict uv' = NoOom uv.

  Parameter uvalue_convert_strict_concat_bytes_inv :
    forall x uv_bytes dt,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_ConcatBytes uv_bytes dt) ->
      exists uv_bytes',
        x = DV1.UVALUE_ConcatBytes uv_bytes' dt /\
          map_monad uvalue_convert_strict uv_bytes' = NoOom uv_bytes.

  Ltac uvalue_convert_strict_inv H :=
    first
      [ apply uvalue_convert_strict_ix_inv in H
      | apply uvalue_convert_strict_iptr_inv in H
      | apply uvalue_convert_strict_addr_inv in H
      | apply uvalue_convert_strict_double_inv in H
      | apply uvalue_convert_strict_float_inv in H
      | apply uvalue_convert_strict_undef_inv in H
      | apply uvalue_convert_strict_poison_inv in H
      | apply uvalue_convert_strict_oom_inv in H
      | apply uvalue_convert_strict_none_inv in H
      | apply uvalue_convert_strict_struct_inv in H
      | apply uvalue_convert_strict_packed_struct_inv in H
      | apply uvalue_convert_strict_array_inv in H
      | apply uvalue_convert_strict_vector_inv in H
      | apply uvalue_convert_strict_ibinop_inv in H
      | apply uvalue_convert_strict_icmp_inv in H
      | apply uvalue_convert_strict_fbinop_inv in H
      | apply uvalue_convert_strict_fcmp_inv in H
      | apply uvalue_convert_strict_conversion_inv in H
      | apply uvalue_convert_strict_gep_inv in H
      | apply uvalue_convert_strict_extract_element_inv in H
      | apply uvalue_convert_strict_insert_element_inv in H
      | apply uvalue_convert_strict_shuffle_vector_inv in H
      | apply uvalue_convert_strict_extract_value_inv in H
      | apply uvalue_convert_strict_insert_value_inv in H
      | apply uvalue_convert_strict_select_inv in H
      | apply uvalue_convert_strict_extract_byte_inv in H
      | apply uvalue_convert_strict_concat_bytes_inv in H
      ];
    try first
      [ destruct H as (?&?&?&?&?&?&?)
      | destruct H as (?&?&?&?&?)
      | destruct H as (?&?&?)
      | destruct H as (?&?)]; subst.

  Ltac uvalue_refine_strict_inv H :=
    rewrite uvalue_refine_strict_equation in H;
    uvalue_convert_strict_inv H.

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

Module DVConvertMake (LP1 : LLVMParams) (LP2 : LLVMParams) (AC : AddrConvert LP1.ADDR LP1.PTOI LP2.ADDR LP2.PTOI) (Events1 : LLVM_INTERACTIONS LP1.ADDR LP1.IP LP1.SIZEOF) (Events2 : LLVM_INTERACTIONS LP2.ADDR LP2.IP LP2.SIZEOF) : DVConvert LP1 LP2 AC Events1 Events2
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

  #[local] Obligation Tactic := try Tactics.program_simpl; try solve [cbn; try lia | solve_dvalue_measure | solve_uvalue_measure].

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


    Fixpoint dvalue_convert_strict (dv1 : DV1.dvalue) : OOM DV2.dvalue
    := match dv1 with
       | DV1.DVALUE_Addr a =>
           a' <- addr_convert a;;
           ret (DV2.DVALUE_Addr a')
       | @DV1.DVALUE_I sz x  => ret (@DV2.DVALUE_I sz x)
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
           fields' <- map_monad dvalue_convert_strict fields;;
           ret (DV2.DVALUE_Struct fields')
       | DV1.DVALUE_Packed_struct fields =>
           fields' <- map_monad dvalue_convert_strict fields;;
           ret (DV2.DVALUE_Packed_struct fields')
       | DV1.DVALUE_Array t elts =>
           elts' <- map_monad dvalue_convert_strict elts;;
           ret (DV2.DVALUE_Array t elts')
       | DV1.DVALUE_Vector t elts =>
           elts' <- map_monad dvalue_convert_strict elts;;
           ret (DV2.DVALUE_Vector t elts')
       end.


  Fixpoint uvalue_convert_strict (uv1 : DV1.uvalue) : OOM DV2.uvalue
    := match uv1 with
       | DV1.UVALUE_Addr a =>
           a' <- addr_convert a;;
           ret (DV2.UVALUE_Addr a')
       | @DV1.UVALUE_I sz x  => ret (@DV2.UVALUE_I sz x)
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
           fields' <- map_monad uvalue_convert_strict fields;;
           ret (DV2.UVALUE_Struct fields')
       | DV1.UVALUE_Packed_struct fields =>
           fields' <- map_monad uvalue_convert_strict fields;;
           ret (DV2.UVALUE_Packed_struct fields')
       | DV1.UVALUE_Array t elts =>
           elts' <- map_monad uvalue_convert_strict elts;;
           ret (DV2.UVALUE_Array t elts')
       | DV1.UVALUE_Vector t elts =>
           elts' <- map_monad uvalue_convert_strict elts;;
           ret (DV2.UVALUE_Vector t elts')
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
           idxs' <- map_monad uvalue_convert_strict idxs;;
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
       | DV1.UVALUE_ShuffleVector dt vec1 vec2 idxmask =>
           vec1' <- uvalue_convert_strict vec1;;
           vec2' <- uvalue_convert_strict vec2;;
           idxmask' <- uvalue_convert_strict idxmask;;
           ret (DV2.UVALUE_ShuffleVector dt vec1' vec2' idxmask')
       | DV1.UVALUE_ExtractValue t vec idxs =>
           vec' <- uvalue_convert_strict vec;;
           ret (DV2.UVALUE_ExtractValue t vec' idxs)
       | DV1.UVALUE_InsertValue t vec et elt idxs =>
           vec' <- uvalue_convert_strict vec;;
           elt' <- uvalue_convert_strict elt;;
           ret (DV2.UVALUE_InsertValue t vec' et elt' idxs)
       | DV1.UVALUE_Select cnd v1 v2 =>
           cnd' <- uvalue_convert_strict cnd;;
           v1' <- uvalue_convert_strict v1;;
           v2' <- uvalue_convert_strict v2;;
           ret (DV2.UVALUE_Select cnd' v1' v2')
       | DV1.UVALUE_ExtractByte uv dt idx sid =>
           uv' <- uvalue_convert_strict uv;;
           ret (DV2.UVALUE_ExtractByte uv' dt idx sid)
       | DV1.UVALUE_ConcatBytes uvs dt =>
           uvs' <- map_monad uvalue_convert_strict uvs;;
           ret (DV2.UVALUE_ConcatBytes uvs' dt)
       end.


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

  (* #[global] Opaque dvalue_convert_strict. *)
  (* #[global] Opaque uvalue_convert_strict. *)
  (* #[global] Opaque dvalue_refine_strict. *)
  (* #[global] Opaque uvalue_refine_strict. *)

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

  Lemma dvalue_refine_strict_dvalue_to_uvalue :
    forall dv1 dv2,
      dvalue_refine_strict dv1 dv2 ->
      uvalue_refine_strict (DV1.dvalue_to_uvalue dv1) (DV2.dvalue_to_uvalue dv2).
  Proof.
   induction dv1; intros dv2 REF;
     unfold dvalue_refine_strict in REF;
     unfold uvalue_refine_strict;
      cbn in *.

    1-12:
      try solve
        [ break_match_hyp; inv REF; cbn; auto
        | inv REF; cbn; auto
        ].

    { (* Structures *)
      break_match_goal; break_match_hyp; inv REF.
      - cbn.
        unfold uvalue_refine_strict in *.
        unfold dvalue_refine_strict in *.
        apply map_monad_oom_Forall2 in Heqo0.
        assert (forall (u : DV1.dvalue) (dv2 : DV2.dvalue),
      In u fields ->
      dvalue_convert_strict u = NoOom dv2 ->
      uvalue_convert_strict (DV1.dvalue_to_uvalue u) = NoOom (DV2.dvalue_to_uvalue dv2)).
        { intros; apply H; auto. }
        clear H.

        eapply Forall2_impl' in H0; eauto.
        apply (Forall2_map_r (fun x y => uvalue_convert_strict (DV1.dvalue_to_uvalue x) = NoOom y) DV2.dvalue_to_uvalue) in H0.
        apply map_monad_oom_Forall2 in Heqo.
        apply Forall2_map_l in Heqo.
        specialize (Forall2_ext_m _ _ _ _ Heqo H0) as EQ.
        subst.
        reflexivity.
      - apply map_monad_OOM_fail in Heqo.
        destruct Heqo as [uv1 [HIN HX]].
        apply Coqlib.list_in_map_inv in HIN.
        destruct HIN as [dv1 [HD HI]].
        apply map_monad_oom_Forall2 in Heqo0.
        specialize (Forall2_In _ _ _ _ HI Heqo0) as X.
        subst.
        destruct X as [dv2 [_ EQ]].
        unfold uvalue_refine_strict in *.
        unfold dvalue_refine_strict in *.
        specialize (H _ HI _ EQ).
        rewrite H in HX. inversion HX.
    }

    { (* Packed Structures *)
      break_match_goal; break_match_hyp; inv REF.
      - cbn.
        unfold uvalue_refine_strict in *.
        unfold dvalue_refine_strict in *.
        apply map_monad_oom_Forall2 in Heqo0.
        assert (forall (u : DV1.dvalue) (dv2 : DV2.dvalue),
      In u fields ->
      dvalue_convert_strict u = NoOom dv2 ->
      uvalue_convert_strict (DV1.dvalue_to_uvalue u) = NoOom (DV2.dvalue_to_uvalue dv2)).
        { intros; apply H; auto. }
        clear H.

        eapply Forall2_impl' in H0; eauto.
        apply (Forall2_map_r (fun x y => uvalue_convert_strict (DV1.dvalue_to_uvalue x) = NoOom y) DV2.dvalue_to_uvalue) in H0.
        apply map_monad_oom_Forall2 in Heqo.
        apply Forall2_map_l in Heqo.
        specialize (Forall2_ext_m _ _ _ _ Heqo H0) as EQ.
        subst.
        reflexivity.
      - apply map_monad_OOM_fail in Heqo.
        destruct Heqo as [uv1 [HIN HX]].
        apply Coqlib.list_in_map_inv in HIN.
        destruct HIN as [dv1 [HD HI]].
        apply map_monad_oom_Forall2 in Heqo0.
        specialize (Forall2_In _ _ _ _ HI Heqo0) as X.
        subst.
        destruct X as [dv2 [_ EQ]].
        unfold uvalue_refine_strict in *.
        unfold dvalue_refine_strict in *.
        specialize (H _ HI _ EQ).
        rewrite H in HX. inversion HX.
    }

    { (* Arrays *)
      break_match_goal; break_match_hyp; inv REF.
      - cbn.
        unfold uvalue_refine_strict in *.
        unfold dvalue_refine_strict in *.
        apply map_monad_oom_Forall2 in Heqo0.
        assert (forall (u : DV1.dvalue) (dv2 : DV2.dvalue),
      In u elts ->
      dvalue_convert_strict u = NoOom dv2 ->
      uvalue_convert_strict (DV1.dvalue_to_uvalue u) = NoOom (DV2.dvalue_to_uvalue dv2)).
        { intros; apply H; auto. }
        clear H.

        eapply Forall2_impl' in H0; eauto.
        apply (Forall2_map_r (fun x y => uvalue_convert_strict (DV1.dvalue_to_uvalue x) = NoOom y) DV2.dvalue_to_uvalue) in H0.
        apply map_monad_oom_Forall2 in Heqo.
        apply Forall2_map_l in Heqo.
        specialize (Forall2_ext_m _ _ _ _ Heqo H0) as EQ.
        subst.
        reflexivity.
      - apply map_monad_OOM_fail in Heqo.
        destruct Heqo as [uv1 [HIN HX]].
        apply Coqlib.list_in_map_inv in HIN.
        destruct HIN as [dv1 [HD HI]].
        apply map_monad_oom_Forall2 in Heqo0.
        specialize (Forall2_In _ _ _ _ HI Heqo0) as X.
        subst.
        destruct X as [dv2 [_ EQ]].
        unfold uvalue_refine_strict in *.
        unfold dvalue_refine_strict in *.
        specialize (H _ HI _ EQ).
        rewrite H in HX. inversion HX.
    }

    { (* Vectors *)
      break_match_goal; break_match_hyp; inv REF.
      - cbn.
        unfold uvalue_refine_strict in *.
        unfold dvalue_refine_strict in *.
        apply map_monad_oom_Forall2 in Heqo0.
        assert (forall (u : DV1.dvalue) (dv2 : DV2.dvalue),
      In u elts ->
      dvalue_convert_strict u = NoOom dv2 ->
      uvalue_convert_strict (DV1.dvalue_to_uvalue u) = NoOom (DV2.dvalue_to_uvalue dv2)).
        { intros; apply H; auto. }
        clear H.

        eapply Forall2_impl' in H0; eauto.
        apply (Forall2_map_r (fun x y => uvalue_convert_strict (DV1.dvalue_to_uvalue x) = NoOom y) DV2.dvalue_to_uvalue) in H0.
        apply map_monad_oom_Forall2 in Heqo.
        apply Forall2_map_l in Heqo.
        specialize (Forall2_ext_m _ _ _ _ Heqo H0) as EQ.
        subst.
        reflexivity.
      - apply map_monad_OOM_fail in Heqo.
        destruct Heqo as [uv1 [HIN HX]].
        apply Coqlib.list_in_map_inv in HIN.
        destruct HIN as [dv1 [HD HI]].
        apply map_monad_oom_Forall2 in Heqo0.
        specialize (Forall2_In _ _ _ _ HI Heqo0) as X.
        subst.
        destruct X as [dv2 [_ EQ]].
        unfold uvalue_refine_strict in *.
        unfold dvalue_refine_strict in *.
        specialize (H _ HI _ EQ).
        rewrite H in HX. inversion HX.
    }
  Qed.

  Hint Resolve dvalue_refine_strict_dvalue_to_uvalue : DVALUE_REFINE.


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
    induction uv; intros uvc b UVC CONC; unfold uvalue_refine_strict, uvalue_convert_strict in UVC;
      try solve
        [ cbn in *; subst; try break_match; inv UVC; cbn; auto
        | cbn in *; subst;
          repeat break_match_hyp_inv;
          eauto
        ]; fold uvalue_convert_strict in *.

    - (* Structs *)
      destruct (map_monad uvalue_convert_strict fields) eqn: EQ.
      + cbn in UVC. inversion UVC. subst. clear UVC.
        cbn.
        unfold uvalue_refine_strict in *.
        apply map_monad_oom_Forall2 in EQ.
        induction EQ.
        * reflexivity.
        * cbn.
          assert (In x (x::l)) by (left; auto).
          destruct (DV1.is_concrete x) eqn:EQX.
          -- rewrite (H x H1 _ true H0); auto. cbn.  eapply IHEQ.
             intros. apply (H u); auto. right. assumption.
          -- rewrite (H x H1 _ false H0); auto.
      + cbn in UVC. inversion UVC.
    - (* Packed Structs *)
      destruct (map_monad uvalue_convert_strict fields) eqn: EQ.
      + cbn in UVC. inversion UVC. subst. clear UVC.
        cbn.
        unfold uvalue_refine_strict in *.
        apply map_monad_oom_Forall2 in EQ.
        induction EQ.
        * reflexivity.
        * cbn.
          assert (In x (x::l)) by (left; auto).
          destruct (DV1.is_concrete x) eqn:EQX.
          -- rewrite (H x H1 _ true H0); auto. cbn.  eapply IHEQ.
             intros. apply (H u); auto. right. assumption.
          -- rewrite (H x H1 _ false H0); auto.
      + cbn in UVC. inversion UVC.
    - (* Arrays *)
      destruct (map_monad uvalue_convert_strict elts) eqn: EQ.
      + cbn in UVC. inversion UVC. subst. clear UVC.
        cbn.
        unfold uvalue_refine_strict in *.
        apply map_monad_oom_Forall2 in EQ.
        induction EQ.
        * reflexivity.
        * cbn.
          assert (In x (x::l)) by (left; auto).
          destruct (DV1.is_concrete x) eqn:EQX.
          -- rewrite (H x H1 _ true H0); auto. cbn.  eapply IHEQ.
             intros. apply (H e); auto. right. assumption.
          -- rewrite (H x H1 _ false H0); auto.
      + cbn in UVC. inversion UVC.
    - (* Vectors *)
      destruct (map_monad uvalue_convert_strict elts) eqn: EQ.
      + cbn in UVC. inversion UVC. subst. clear UVC.
        cbn.
        unfold uvalue_refine_strict in *.
        apply map_monad_oom_Forall2 in EQ.
        induction EQ.
        * reflexivity.
        * cbn.
          assert (In x (x::l)) by (left; auto).
          destruct (DV1.is_concrete x) eqn:EQX.
          -- rewrite (H x H1 _ true H0); auto. cbn.  eapply IHEQ.
             intros. apply (H e); auto. right. assumption.
          -- rewrite (H x H1 _ false H0); auto.
      + cbn in UVC. inversion UVC.
  Qed.


  (** Lemmas about uvalue_to_dvalue *)

  Lemma uvalue_to_dvalue_dvalue_refine_strict :
    forall uv1 uv2 dv1,
      uvalue_refine_strict uv1 uv2 ->
      DV1.uvalue_to_dvalue uv1 = inr dv1 ->
      exists dv2, DV2.uvalue_to_dvalue uv2 = inr dv2 /\
               dvalue_refine_strict dv1 dv2.
  Proof.
    unfold uvalue_refine_strict.
    unfold dvalue_refine_strict.
    induction uv1;
      intros uv2 dv1 CONV UV1;
      try solve
        [ cbn;
          cbn in CONV;
          (repeat break_match_hyp_inv;
           try solve
             [ cbn in *;
               inv UV1;
               repeat break_match_hyp_inv;
               try (inv CONV);
               eexists; cbn; split; eauto;
               cbn; try rewrite Heqo; auto
        ])].

    - (* Structures *)
      cbn in *.
      repeat break_match_hyp_inv.
      cbn.
      apply map_monad_oom_Forall2 in Heqo.
      apply map_monad_err_Forall2 in Heqs.
      revert H l Heqs.
      induction Heqo; intros; inversion Heqs; subst.
      + exists (DV2.DVALUE_Struct []).
        auto.
      + forward IHHeqo.
        { intros. eapply H0; auto. right. apply H1. auto. auto. }
        apply IHHeqo in H5.
        destruct H5 as [dv [EQ1 EQ2]].
        repeat break_match_hyp_inv.
        assert (In x (x::l)) by (left; auto).
        specialize (H0 x H1 _ _ H H3).
        destruct H0 as [dv1 [HDV HCV]].
        exists (DV2.DVALUE_Struct (dv1 :: l0)).
        split; cbn.
        rewrite HDV. rewrite Heqs0. reflexivity.
        rewrite HCV. rewrite Heqo0. reflexivity.

    - (* Packed structures *)
      cbn in *.
      repeat break_match_hyp_inv.
      cbn.
      apply map_monad_oom_Forall2 in Heqo.
      apply map_monad_err_Forall2 in Heqs.
      revert H l Heqs.
      induction Heqo; intros; inversion Heqs; subst.
      + exists (DV2.DVALUE_Packed_struct []).
        auto.
      + forward IHHeqo.
        { intros. eapply H0; auto. right. apply H1. auto. auto. }
        apply IHHeqo in H5.
        destruct H5 as [dv [EQ1 EQ2]].
        repeat break_match_hyp_inv.
        assert (In x (x::l)) by (left; auto).
        specialize (H0 x H1 _ _ H H3).
        destruct H0 as [dv1 [HDV HCV]].
        exists (DV2.DVALUE_Packed_struct (dv1 :: l0)).
        split; cbn.
        rewrite HDV. rewrite Heqs0. reflexivity.
        rewrite HCV. rewrite Heqo0. reflexivity.

    - (* Arrays cons *)
      cbn in *.
      repeat break_match_hyp_inv.
      cbn.
      apply map_monad_oom_Forall2 in Heqo.
      apply map_monad_err_Forall2 in Heqs.
      revert H l Heqs.
      induction Heqo; intros; inversion Heqs; subst.
      + exists (DV2.DVALUE_Array t []).
        auto.
      + forward IHHeqo.
        { intros. eapply H0; auto. right. apply H1. auto. auto. }
        apply IHHeqo in H5.
        destruct H5 as [dv [EQ1 EQ2]].
        repeat break_match_hyp_inv.
        assert (In x (x::l)) by (left; auto).
        specialize (H0 x H1 _ _ H H3).
        destruct H0 as [dv1 [HDV HCV]].
        exists (DV2.DVALUE_Array t (dv1 :: l0)).
        split; cbn.
        rewrite HDV. rewrite Heqs0. reflexivity.
        rewrite HCV. rewrite Heqo0. reflexivity.

    - (* Vectors cons *)
      cbn in *.
      repeat break_match_hyp_inv.
      cbn.
      apply map_monad_oom_Forall2 in Heqo.
      apply map_monad_err_Forall2 in Heqs.
      revert H l Heqs.
      induction Heqo; intros; inversion Heqs; subst.
      + exists (DV2.DVALUE_Vector t []).
        auto.
      + forward IHHeqo.
        { intros. eapply H0; auto. right. apply H1. auto. auto. }
        apply IHHeqo in H5.
        destruct H5 as [dv [EQ1 EQ2]].
        repeat break_match_hyp_inv.
        assert (In x (x::l)) by (left; auto).
        specialize (H0 x H1 _ _ H H3).
        destruct H0 as [dv1 [HDV HCV]].
        exists (DV2.DVALUE_Vector t (dv1 :: l0)).
        split; cbn.
        rewrite HDV. rewrite Heqs0. reflexivity.
        rewrite HCV. rewrite Heqo0. reflexivity.
  Qed.

  Lemma uvalue_to_dvalue_dvalue_refine_strict_error :
    forall uv1 uv2 s,
      uvalue_refine_strict uv1 uv2 ->
      DV1.uvalue_to_dvalue uv1 = inl s ->
      exists s', DV2.uvalue_to_dvalue uv2 = inl s'.
  Proof.
    unfold uvalue_refine_strict.
    unfold dvalue_refine_strict.
    induction uv1;
      intros uv2 dv1 CONV UV1;
      try solve
        [ cbn;
          cbn in CONV;
          (repeat break_match_hyp_inv;
           try solve
             [ cbn in *;
               inv UV1;
               repeat break_match_hyp_inv;
               try (inv CONV);
               eexists; cbn; split; eauto;
               cbn; try rewrite Heqo; auto
        ])].

    - (* Structures *)
      cbn in *.
      repeat break_match_hyp_inv.
      cbn.
      apply map_monad_oom_Forall2 in Heqo.
      revert H dv1 Heqs.
      induction Heqo; intros; cbn in *.
      + inversion Heqs.
      + repeat break_match_hyp_inv.
        * forward (H0 x). left; reflexivity.
          specialize (H0 _ dv1 H Heqs0).
          destruct H0 as [s' EQS].
          rewrite EQS. exists s'. reflexivity.
        * forward IHHeqo.
          intros.
          eapply H0. right; eassumption. auto. eauto.
          destruct (IHHeqo dv1) as [s HS].
          reflexivity.
          break_match_hyp_inv.
          break_match_goal.
          -- eexists; eauto.
          -- break_match_hyp_inv.

    - cbn in *.
      repeat break_match_hyp_inv.
      cbn.
      apply map_monad_oom_Forall2 in Heqo.
      revert H dv1 Heqs.
      induction Heqo; intros; cbn in *.
      + inversion Heqs.
      + repeat break_match_hyp_inv.
        * forward (H0 x). left; reflexivity.
          specialize (H0 _ dv1 H Heqs0).
          destruct H0 as [s' EQS].
          rewrite EQS. exists s'. reflexivity.
        * forward IHHeqo.
          intros.
          eapply H0. right; eassumption. auto. eauto.
          destruct (IHHeqo dv1) as [s HS].
          reflexivity.
          break_match_hyp_inv.
          break_match_goal.
          -- eexists; eauto.
          -- break_match_hyp_inv.
    -       cbn in *.
      repeat break_match_hyp_inv.
      cbn.
      apply map_monad_oom_Forall2 in Heqo.
      revert H dv1 Heqs.
      induction Heqo; intros; cbn in *.
      + inversion Heqs.
      + repeat break_match_hyp_inv.
        * forward (H0 x). left; reflexivity.
          specialize (H0 _ dv1 H Heqs0).
          destruct H0 as [s' EQS].
          rewrite EQS. exists s'. reflexivity.
        * forward IHHeqo.
          intros.
          eapply H0. right; eassumption. auto. eauto.
          destruct (IHHeqo dv1) as [s HS].
          reflexivity.
          break_match_hyp_inv.
          break_match_goal.
          -- eexists; eauto.
          -- break_match_hyp_inv.
    - cbn in *.
      repeat break_match_hyp_inv.
      cbn.
      apply map_monad_oom_Forall2 in Heqo.
      revert H dv1 Heqs.
      induction Heqo; intros; cbn in *.
      + inversion Heqs.
      + repeat break_match_hyp_inv.
        * forward (H0 x). left; reflexivity.
          specialize (H0 _ dv1 H Heqs0).
          destruct H0 as [s' EQS].
          rewrite EQS. exists s'. reflexivity.
        * forward IHHeqo.
          intros.
          eapply H0. right; eassumption. auto. eauto.
          destruct (IHHeqo dv1) as [s HS].
          reflexivity.
          break_match_hyp_inv.
          break_match_goal.
          -- eexists; eauto.
          -- break_match_hyp_inv.
  Qed.


  (** Lemmas about default dvalues *)

  Lemma default_dvalue_of_dtyp_i_dv1_dv2_equiv :
    forall sz v1,
      DV1.default_dvalue_of_dtyp_i sz = v1 ->
      exists v2,
        DV2.default_dvalue_of_dtyp_i sz = v2 /\ dvalue_refine_strict v1 v2.
  Proof.
    intros sz v1 V1.
    cbn in *; inv V1;
      (eexists; split; [eauto | unfold dvalue_refine_strict; auto]).
  Qed.

  Lemma default_dvalue_of_dtyp_i_dv1_dv2_equiv' :
    forall sz v2,
      DV2.default_dvalue_of_dtyp_i sz = v2 ->
      exists v1,
        DV1.default_dvalue_of_dtyp_i sz = v1 /\ dvalue_refine_strict v1 v2.
  Proof.
    intros sz v2 V2.
    cbn in *; inv V2;
      (eexists; split; [eauto | unfold dvalue_refine_strict; auto]).
  Qed.

  Lemma default_dvalue_of_dtyp_dv1_dv2_equiv :
    forall dt v1,
      DV1.default_dvalue_of_dtyp dt = inr v1 ->
      exists v2, DV2.default_dvalue_of_dtyp dt = inr v2 /\ dvalue_refine_strict v1 v2.
  Proof.
    unfold dvalue_refine_strict.
    induction dt; intros v1 V1;
      try solve
        [
          cbn in *; inv V1;
          eexists; split; eauto;
          cbn;
          auto
        ].
    - cbn in *; inv V1;
        eexists; split; eauto.
      cbn.
      rewrite LP1.IP.to_Z_0.
      rewrite LP2.IP.from_Z_0.
      auto.
    - cbn in *; inv V1;
        eexists; split; eauto.
      cbn.
      rewrite addr_convert_null.
      reflexivity.
    - (* Arrays *)
      cbn in *.
      break_match_hyp_inv.
      specialize (IHdt d eq_refl) as [v2 [DEFv2 REFv2]].
      eexists.
      rewrite DEFv2; split; eauto.
      cbn.
      break_match.
      2: {
        apply map_monad_OOM_fail in Heqo.
        destruct Heqo as [a [IN CONVa]].
        apply repeat_spec in IN; subst.
        rewrite REFv2 in CONVa.
        inv CONVa.
      }
      apply map_monad_oom_Forall2 in Heqo.
      eapply Forall2_repeat_OOM with (b:=v2) in Heqo; auto.
      rewrite Heqo.
      reflexivity.

    - (* Structs *)
      cbn in *.
      break_match_hyp_inv.
      apply map_monad_err_Forall2 in Heqs.
      revert H.
      induction Heqs; intros; cbn.
      + exists (DV2.DVALUE_Struct []); auto.
      + forward IHHeqs.
        { intros. eapply H0; auto. right. apply H1. }
        destruct IHHeqs as [v2 [EQ1 EQ2]].
        cbn in EQ2.
        repeat break_match_hyp_inv.
        assert (In x (x::l)) by (left; auto).
        specialize (H0 x H1 y H).
        destruct H0 as [dv1 [HDV HCV]].
        exists (DV2.DVALUE_Struct (dv1 :: l0)).
        split; cbn.
        rewrite HDV. reflexivity.
        rewrite HCV. reflexivity.
    - (* Structs *)
      cbn in *.
      break_match_hyp_inv.
      apply map_monad_err_Forall2 in Heqs.
      revert H.
      induction Heqs; intros; cbn.
      + exists (DV2.DVALUE_Packed_struct []); auto.
      + forward IHHeqs.
        { intros. eapply H0; auto. right. apply H1. }
        destruct IHHeqs as [v2 [EQ1 EQ2]].
        cbn in EQ2.
        repeat break_match_hyp_inv.
        assert (In x (x::l)) by (left; auto).
        specialize (H0 x H1 y H).
        destruct H0 as [dv1 [HDV HCV]].
        exists (DV2.DVALUE_Packed_struct (dv1 :: l0)).
        split; cbn.
        rewrite HDV. reflexivity.
        rewrite HCV. reflexivity.
    - (* Vectors *)
      cbn in V1.
      repeat break_match_hyp_inv; cbn in *.
      + specialize (IHdt _ eq_refl).
        destruct IHdt as [dv2 [EQ1 EQ2]].
        inv EQ1.
        break_match_goal.
        2: {
          apply map_monad_OOM_fail in Heqo.
          destruct Heqo as [a [IN CONVa]].
          apply repeat_spec in IN; subst.
          rewrite EQ2 in CONVa.
          inv CONVa.
        }
        apply map_monad_oom_Forall2 in Heqo.
        eapply Forall2_repeat_OOM with (b:=(DV2.default_dvalue_of_dtyp_i sz0)) in Heqo; auto.
        rewrite Heqo.
        eexists; eauto.
      + cbn in *.
        specialize (IHdt (DV1.DVALUE_IPTR LP1.IP.zero) eq_refl).
        destruct IHdt as [dv2 [EQ1 EQ2]].
        exists (DV2.DVALUE_Vector (DTYPE_Vector sz DTYPE_IPTR) (repeat (DV2.DVALUE_IPTR LP2.IP.zero) (N.to_nat sz))).
        split; auto.
        break_match_goal.
        2 : {
          apply map_monad_OOM_fail in Heqo.
          destruct Heqo as [a [IN CONVa]].
          apply repeat_spec in IN; subst.
          cbn in CONVa.
          break_match_hyp_inv.
          cbn in EQ2.
          break_match_hyp_inv.
          inversion Heqo.
        }
        apply map_monad_oom_Forall2 in Heqo.
        eapply Forall2_repeat_OOM with (b:=dv2) in Heqo; auto.
        rewrite Heqo.
        cbn in EQ2.
        break_match_hyp_inv.
        inversion EQ1.
        auto.
      + cbn in *.
        specialize (IHdt (DV1.DVALUE_Addr LP1.ADDR.null) eq_refl).
        destruct IHdt as [dv2 [EQ1 EQ2]].
        exists (DV2.DVALUE_Vector (DTYPE_Vector sz DTYPE_Pointer) (repeat (DV2.DVALUE_Addr LP2.ADDR.null) (N.to_nat sz))).
        split; auto.
        break_match_goal.
        2 : {
          apply map_monad_OOM_fail in Heqo.
          destruct Heqo as [a [IN CONVa]].
          apply repeat_spec in IN; subst.
          cbn in CONVa.
          break_match_hyp_inv.
          cbn in EQ2.
          break_match_hyp_inv.
          inversion Heqo.
        }
        apply map_monad_oom_Forall2 in Heqo.
        eapply Forall2_repeat_OOM with (b:=dv2) in Heqo; auto.
        rewrite Heqo.
        cbn in EQ2.
        break_match_hyp_inv.
        inversion EQ1.
        auto.
      + cbn in *.
        specialize (IHdt (DV1.DVALUE_Float Floats.Float32.zero) eq_refl).
        destruct IHdt as [dv2 [EQ1 EQ2]].
        eexists. split; [reflexivity|].
        break_match_goal.
        2 : {
          apply map_monad_OOM_fail in Heqo.
          destruct Heqo as [a [IN CONVa]].
          apply repeat_spec in IN; subst.
          cbn in CONVa.
          inversion CONVa.
        }
        apply map_monad_oom_Forall2 in Heqo.
        eapply Forall2_repeat_OOM with (b:=dv2) in Heqo; auto.
        rewrite Heqo.
        cbn in EQ2.
        inversion EQ1.
        auto.
      + cbn in *.
        specialize (IHdt (DV1.DVALUE_Double (Floats.Float32.to_double Floats.Float32.zero)) eq_refl).
        destruct IHdt as [dv2 [EQ1 EQ2]].
        eexists. split; [reflexivity|].
        break_match_goal.
        2 : {
          apply map_monad_OOM_fail in Heqo.
          destruct Heqo as [a [IN CONVa]].
          apply repeat_spec in IN; subst.
          cbn in CONVa.
          inversion CONVa.
        }
        apply map_monad_oom_Forall2 in Heqo.
        eapply Forall2_repeat_OOM with (b:=dv2) in Heqo; auto.
        rewrite Heqo.
        cbn in EQ2.
        inversion EQ1.
        auto.
  Qed.

  Lemma default_dvalue_of_dtyp_dv1_dv2_equiv' :
    forall dt v2,
      DV2.default_dvalue_of_dtyp dt = inr v2 ->
      exists v1, DV1.default_dvalue_of_dtyp dt = inr v1 /\ dvalue_refine_strict v1 v2.
  Proof.
    unfold dvalue_refine_strict.
    induction dt; intros v2 V2;
      try solve
        [
          cbn in *; inv V2;
          eexists; split; eauto;
          cbn;
          auto
        ].
    - cbn in *; inv V2;
        eexists; split; eauto.
      cbn.
      rewrite LP1.IP.to_Z_0.
      rewrite LP2.IP.from_Z_0.
      auto.
    - cbn in *; inv V2;
        eexists; split; eauto.
      cbn.
      rewrite addr_convert_null.
      reflexivity.
    - (* Arrays *)
      cbn in *.
      break_match_hyp; inv V2.
      specialize (IHdt d eq_refl) as [v1 [DEFv1 REFv1]].
      eexists.
      rewrite DEFv1; split; eauto.
      cbn.
      break_match.
      2: {
          apply map_monad_OOM_fail in Heqo.
          destruct Heqo as [a [IN CONVa]].
          apply repeat_spec in IN; subst.
          cbn in CONVa.
          rewrite REFv1 in CONVa.
          inversion CONVa.
        }
        apply map_monad_oom_Forall2 in Heqo.
        eapply Forall2_repeat_OOM with (b:=d) in Heqo; auto.
        rewrite Heqo.
        auto.

    - cbn in *.
      break_match_hyp_inv.
      apply map_monad_err_Forall2 in Heqs.
      revert H.
      induction Heqs; intros; cbn.
      + exists (DV1.DVALUE_Struct []); auto.
      + forward IHHeqs.
        { intros. eapply H0; auto. right. apply H1. }
        destruct IHHeqs as [v2 [EQ1 EQ2]].
        cbn in EQ2.
        repeat break_match_hyp_inv.
        assert (In x (x::l)) by (left; auto).
        specialize (H0 x H1 y H).
        destruct H0 as [dv1 [HDV HCV]].
        exists (DV1.DVALUE_Struct (dv1 :: l0)).
        split; cbn in *.
        rewrite HDV. reflexivity.
        rewrite HCV.
        break_match_hyp_inv.
        reflexivity.

    -  cbn in *.
      break_match_hyp_inv.
      apply map_monad_err_Forall2 in Heqs.
      revert H.
      induction Heqs; intros; cbn.
      + exists (DV1.DVALUE_Packed_struct []); auto.
      + forward IHHeqs.
        { intros. eapply H0; auto. right. apply H1. }
        destruct IHHeqs as [v2 [EQ1 EQ2]].
        cbn in EQ2.
        repeat break_match_hyp_inv.
        assert (In x (x::l)) by (left; auto).
        specialize (H0 x H1 y H).
        destruct H0 as [dv1 [HDV HCV]].
        exists (DV1.DVALUE_Packed_struct (dv1 :: l0)).
        split; cbn in *.
        rewrite HDV. reflexivity.
        rewrite HCV.
        break_match_hyp_inv.
        reflexivity.

    - cbn in V2.
      repeat break_match_hyp_inv; cbn in *.
      + specialize (IHdt _ eq_refl).
        destruct IHdt as [dv2 [EQ1 EQ2]].
        inv EQ1.
        eexists; split; [reflexivity|].
        cbn in *.
        inv EQ2.
        break_match_goal.
        2: {
          apply map_monad_OOM_fail in Heqo.
          destruct Heqo as [a [IN CONVa]].
          apply repeat_spec in IN; subst.
          inv CONVa.
        }
        apply map_monad_oom_Forall2 in Heqo.
        eapply Forall2_repeat_OOM with (b:=(DV2.default_dvalue_of_dtyp_i sz0)) in Heqo; auto.
        rewrite Heqo.
        eexists; eauto.

      + specialize (IHdt _ eq_refl).
        destruct IHdt as [dv2 [EQ1 EQ2]].
        inv EQ1.
        eexists; split; [reflexivity|].
        cbn in *.
        inv EQ2.
        break_match_goal.
        2: {
          apply map_monad_OOM_fail in Heqo.
          destruct Heqo as [a [IN CONVa]].
          apply repeat_spec in IN; subst.
          inv CONVa.
          rewrite H0 in H1; inv H1.
        }
        apply map_monad_oom_Forall2 in Heqo.
        eapply Forall2_repeat_OOM in Heqo; auto.
        rewrite Heqo.
        eexists; eauto.
        cbn; rewrite H0; auto.
      + cbn in *.
        specialize (IHdt (DV2.DVALUE_Addr LP2.ADDR.null) eq_refl).
        destruct IHdt as [dv2 [EQ1 EQ2]].
        inversion EQ1; subst.
        cbn in *.
        eexists; split; [reflexivity|].
        cbn in *.
        break_match_hyp_inv.
        break_match_goal.
        2 : {
          apply map_monad_OOM_fail in Heqo0.
          destruct Heqo0 as [a [IN CONVa]].
          apply repeat_spec in IN; subst.
          cbn in *.
          break_match_hyp_inv.
          rewrite addr_convert_null in Heqo0.
          inversion Heqo0.
        }
        apply map_monad_oom_Forall2 in Heqo0.
        eapply Forall2_repeat_OOM  in Heqo0; auto.
        rewrite Heqo0. reflexivity.
        cbn.
        break_match_goal. inversion Heqo. reflexivity.
        inversion Heqo.

      + cbn in *.
        specialize (IHdt (DV2.DVALUE_Float Floats.Float32.zero) eq_refl).
        destruct IHdt as [dv2 [EQ1 EQ2]].
        eexists. split; [reflexivity|].
        cbn in *.
        break_match_goal.
        2 : {
          apply map_monad_OOM_fail in Heqo.
          destruct Heqo as [a [IN CONVa]].
          apply repeat_spec in IN; subst.
          cbn in CONVa.
          inversion CONVa.
        }
        apply map_monad_oom_Forall2 in Heqo.
        eapply Forall2_repeat_OOM in Heqo.
        rewrite Heqo. reflexivity.
        cbn.  reflexivity.

      + cbn in *.
        specialize (IHdt (DV2.DVALUE_Double (Floats.Float32.to_double Floats.Float32.zero)) eq_refl).
        destruct IHdt as [dv2 [EQ1 EQ2]].
        eexists. split; [reflexivity|].
        cbn in *.
        break_match_goal.
        2 : {
          apply map_monad_OOM_fail in Heqo.
          destruct Heqo as [a [IN CONVa]].
          apply repeat_spec in IN; subst.
          cbn in CONVa.
          inversion CONVa.
        }
        apply map_monad_oom_Forall2 in Heqo.
        eapply Forall2_repeat_OOM in Heqo.
        rewrite Heqo. reflexivity.
        cbn.
        reflexivity.
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
    }

    { induction dt; cbn in *;
        try solve [inv S; auto].
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
    }
  Qed.

  Lemma dvalue_refine_strict_R2_injective :
    R2_injective dvalue_refine_strict.
  Proof.
    red.
    unfold dvalue_refine_strict.
    intros r1 r2 a b R1R2 AB.
    split; intros EQ; subst.
    - rewrite R1R2 in AB. inv AB.
      auto.
    - generalize dependent r2.
      generalize dependent a.
      induction r1; intros a'; induction a'; intros r2 R1R2 AB;
        try
          solve
          [ unfold dvalue_refine_strict;
            cbn in *;
            break_match_hyp; inv AB;
            break_match_hyp; inv R1R2;
            pose proof (addr_convert_injective _ _ _ Heqo0 Heqo);
            subst; auto
          | unfold dvalue_refine_strict;
            cbn in *;
            break_match_hyp; inv R1R2;
            inv AB
          | unfold dvalue_refine_strict;
            cbn in *;
            inv AB; inv R1R2; auto
          | unfold dvalue_refine_strict;
            cbn in *;
            break_match_hyp; inv AB;
            break_match_hyp; inv R1R2;
            apply LP2.IP.from_Z_to_Z in Heqo, Heqo0;
            rewrite Heqo in Heqo0;
            apply LP1.IP.to_Z_inj in Heqo0;
            subst;
            auto
          | unfold dvalue_refine_strict;
            cbn in R1R2;
            break_match_hyp; inv R1R2;
            inv AB
          | unfold dvalue_refine_strict;
            cbn in *;
            break_match_hyp; inv AB;
            break_match_hyp; inv R1R2
          ].

      { (* Structs *)
        cbn in *;
          break_match_hyp; inv AB;
          break_match_hyp; inv R1R2.

        clear H0.
        apply map_monad_oom_Forall2 in Heqo0.
        apply map_monad_oom_Forall2 in Heqo.

        assert (fields = fields0).
        { eapply Forall2_inj_OOM_l; eauto. }
        rewrite H0.
        reflexivity.
      }

      { (* Packed Structs *)
        cbn in *;
          break_match_hyp; inv AB;
          break_match_hyp; inv R1R2.

        clear H0.
        apply map_monad_oom_Forall2 in Heqo0.
        apply map_monad_oom_Forall2 in Heqo.
        assert (fields = fields0).
        { eapply Forall2_inj_OOM_l; eauto. }
        rewrite H0.
        reflexivity.
      }

      { (* Arrays *)
        cbn in *;
          break_match_hyp; inv AB;
          break_match_hyp; inv R1R2.

        clear H0.
        apply map_monad_oom_Forall2 in Heqo0.
        apply map_monad_oom_Forall2 in Heqo.
        assert (elts = elts0).
        { eapply Forall2_inj_OOM_l; eauto. }
        rewrite H0.
        reflexivity.
      }

      { (* Vectors *)
        cbn in *;
          break_match_hyp; inv AB;
          break_match_hyp; inv R1R2.

        clear H0.
        apply map_monad_oom_Forall2 in Heqo0.
        apply map_monad_oom_Forall2 in Heqo.
        assert (elts = elts0).
        { eapply Forall2_inj_OOM_l; eauto. }
        rewrite H0.
        reflexivity.
      }
  Qed.


  Lemma uvalue_refine_strict_R2_injective :
    R2_injective uvalue_refine_strict.
  Proof.
    red.
    unfold uvalue_refine_strict.
    intros r1 r2 a b R1R2 AB.
    split; intros EQ; subst.
    - rewrite R1R2 in AB. inv AB.
      auto.
    - generalize dependent r2.
      generalize dependent a.
      induction r1; intros a'; destruct a'; intros r2 R1R2 AB; cbn in *; repeat break_match_hyp_inv;
        try solve
          [ inversion AB
          | inversion R1R2
          | rewrite <- R1R2 in AB; inversion AB; subst; auto
          ];
        try (erewrite <- IHr1; eauto);
        try (erewrite <- IHr1_1; eauto);
        try (erewrite <- IHr1_2; eauto);
        try (erewrite <- IHr1_3; eauto).

      + (* addresses *)
        pose proof (addr_convert_injective _ _ _ Heqo0 Heqo);
         subst; auto.

      + (* IPTR *)
        apply LP2.IP.from_Z_to_Z in Heqo, Heqo0;
         rewrite Heqo in Heqo0;
         apply LP1.IP.to_Z_inj in Heqo0;
         subst;
         auto.

     +  (* Structs *)
        apply map_monad_oom_Forall2 in Heqo0.
        apply map_monad_oom_Forall2 in Heqo.

        assert (fields = fields0).
        { eapply Forall2_inj_OOM_l; eauto. }
        rewrite H0.
        reflexivity.

     +  (* Packed_structs *)
        apply map_monad_oom_Forall2 in Heqo0.
        apply map_monad_oom_Forall2 in Heqo.

        assert (fields = fields0).
        { eapply Forall2_inj_OOM_l; eauto. }
        rewrite H0.
        reflexivity.

     +  (* Arrays *)
        apply map_monad_oom_Forall2 in Heqo0.
        apply map_monad_oom_Forall2 in Heqo.
        assert (elts = elts0).
        { eapply Forall2_inj_OOM_l; eauto. }
        rewrite H0.
        reflexivity.

     +  (* Vectors *)
        apply map_monad_oom_Forall2 in Heqo0.
        apply map_monad_oom_Forall2 in Heqo.
        assert (elts = elts0).
        { eapply Forall2_inj_OOM_l; eauto. }
        rewrite H0.
        reflexivity.

     + apply map_monad_oom_Forall2 in Heqo0.
       apply map_monad_oom_Forall2 in Heqo2.
       assert (idxs = idxs0).
       { eapply Forall2_inj_OOM_l; eauto. }
       rewrite H0.
       reflexivity.

     + apply map_monad_oom_Forall2 in Heqo0.
       apply map_monad_oom_Forall2 in Heqo.
       assert (uvs = uvs0).
       { eapply Forall2_inj_OOM_l; eauto. }
       rewrite H0.
       reflexivity.
  Qed.

  Lemma dvalue_convert_strict_addr_inv :
    forall x a,
      dvalue_convert_strict x = NoOom (DV2.DVALUE_Addr a) ->
      exists a',
        AC.addr_convert a' = NoOom a /\
          x = DV1.DVALUE_Addr a'.
  Proof.
    intros x a H.
    destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
    break_match_hyp; inv H1.
    exists a0; auto.
  Qed.

  Lemma dvalue_convert_strict_iptr_inv :
    forall x n,
      dvalue_convert_strict x = NoOom (DV2.DVALUE_IPTR n) ->
      exists n',
        LP2.IP.from_Z (LP1.IP.to_Z n') = NoOom n /\
          x = DV1.DVALUE_IPTR n'.
  Proof.
    intros x n H.
    destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
    break_match_hyp; inv H1.
    exists x; auto.
  Qed.

  Lemma dvalue_convert_strict_ix_inv :
    forall sz x n,
      dvalue_convert_strict x = NoOom (@DV2.DVALUE_I sz n) ->
      x = @DV1.DVALUE_I sz n.
  Proof.
    intros sz x n H.
    destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
    subst.
    auto.
  Qed.

  Lemma dvalue_convert_strict_double_inv :
    forall x v,
      dvalue_convert_strict x = NoOom (DV2.DVALUE_Double v) ->
      x = DV1.DVALUE_Double v.
  Proof.
    intros x n H.
    destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
    subst.
    auto.
  Qed.

  Lemma dvalue_convert_strict_float_inv :
    forall x v,
      dvalue_convert_strict x = NoOom (DV2.DVALUE_Float v) ->
      x = DV1.DVALUE_Float v.
  Proof.
    intros x n H.
    destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
    subst.
    auto.
  Qed.

  Lemma dvalue_convert_strict_poison_inv :
    forall x v,
      dvalue_convert_strict x = NoOom (DV2.DVALUE_Poison v) ->
      x = DV1.DVALUE_Poison v.
  Proof.
    intros x n H.
    destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
    subst.
    auto.
  Qed.

  Lemma dvalue_convert_strict_oom_inv :
    forall x v,
      dvalue_convert_strict x = NoOom (DV2.DVALUE_Oom v) ->
      x = DV1.DVALUE_Oom v.
  Proof.
    intros x n H.
    destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
    subst.
    auto.
  Qed.

  Lemma dvalue_convert_strict_none_inv :
    forall x,
      dvalue_convert_strict x = NoOom DV2.DVALUE_None ->
      x = DV1.DVALUE_None.
  Proof.
    intros x H.
    destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
    subst.
    auto.
  Qed.

  Lemma dvalue_convert_strict_struct_inv :
    forall x fields,
      dvalue_convert_strict x = NoOom (DV2.DVALUE_Struct fields) ->
      exists fields',
        x = DV1.DVALUE_Struct fields' /\
          map_monad dvalue_convert_strict fields' = NoOom fields.
  Proof.
    intros x fields H.
    destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
    break_match_hyp; inv H1.
    exists fields0.
    split; auto.
  Qed.

  Lemma dvalue_convert_strict_packed_struct_inv :
    forall x fields,
      dvalue_convert_strict x = NoOom (DV2.DVALUE_Packed_struct fields) ->
      exists fields',
        x = DV1.DVALUE_Packed_struct fields' /\
          map_monad dvalue_convert_strict fields' = NoOom fields.
  Proof.
    intros x fields H.
    destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
    break_match_hyp; inv H1.
    exists fields0.
    split; auto.
  Qed.

  Lemma dvalue_convert_strict_array_inv :
    forall x elts t,
      dvalue_convert_strict x = NoOom (DV2.DVALUE_Array t elts) ->
      exists elts',
        x = DV1.DVALUE_Array t elts' /\
          map_monad dvalue_convert_strict elts' = NoOom elts.
  Proof.
    intros x elts t H.
    destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
    break_match_hyp; inv H1.
    exists elts0.
    split; auto.
  Qed.

  Lemma dvalue_convert_strict_vector_inv :
    forall x elts t,
      dvalue_convert_strict x = NoOom (DV2.DVALUE_Vector t elts) ->
      exists elts',
        x = DV1.DVALUE_Vector t elts' /\
          map_monad dvalue_convert_strict elts' = NoOom elts.
  Proof.
    intros x elts t H.
    destruct x; inversion H; try solve [ break_match_hyp; inv H1 ].
    break_match_hyp; inv H1.
    exists elts0.
    split; auto.
  Qed.

  Ltac dvalue_convert_strict_inv H :=
    first
      [ apply dvalue_convert_strict_ix_inv in H
      | apply dvalue_convert_strict_iptr_inv in H
      | apply dvalue_convert_strict_addr_inv in H
      | apply dvalue_convert_strict_double_inv in H
      | apply dvalue_convert_strict_float_inv in H
      | apply dvalue_convert_strict_poison_inv in H
      | apply dvalue_convert_strict_oom_inv in H
      | apply dvalue_convert_strict_none_inv in H
      | apply dvalue_convert_strict_struct_inv in H
      | apply dvalue_convert_strict_packed_struct_inv in H
      | apply dvalue_convert_strict_array_inv in H
      | apply dvalue_convert_strict_vector_inv in H
      ];
    try first [destruct H as (?&?&?)
          | destruct H as (?&?)]; subst.

  Ltac dvalue_refine_strict_inv H :=
    rewrite dvalue_refine_strict_equation in H;
    dvalue_convert_strict_inv H.

  (** Uvalue Inversion Lemmas *)
  Lemma uvalue_convert_strict_addr_inv :
    forall x a,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_Addr a) ->
      exists a',
        AC.addr_convert a' = NoOom a /\
          x = DV1.UVALUE_Addr a'.
  Proof.
    intros x a H.
    induction x;
      repeat red in H; cbn in H;
      repeat break_match_hyp_inv;
      try inv H;
      eauto.
  Qed.

  Lemma uvalue_convert_strict_iptr_inv :
    forall x n,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_IPTR n) ->
      exists n',
        LP2.IP.from_Z (LP1.IP.to_Z n') = NoOom n /\
          x = DV1.UVALUE_IPTR n'.
  Proof.
    intros x a H.
    induction x;
      repeat red in H; cbn in H;
      repeat break_match_hyp_inv;
      try inv H;
      eauto.
  Qed.

  Lemma uvalue_convert_strict_ix_inv :
    forall sz x n,
      uvalue_convert_strict x = NoOom (@DV2.UVALUE_I sz n) ->
      x = @DV1.UVALUE_I sz n.
  Proof.
    intros sz x a H.
    induction x;
      repeat red in H; cbn in H;
      repeat break_match_hyp_inv;
      try inv H;
      eauto.
  Qed.

  Lemma uvalue_convert_strict_double_inv :
    forall x v,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_Double v) ->
      x = DV1.UVALUE_Double v.
  Proof.
    intros x a H.
    induction x;
      repeat red in H; cbn in H;
      repeat break_match_hyp_inv;
      try inv H;
      eauto.
  Qed.

  Lemma uvalue_convert_strict_float_inv :
    forall x v,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_Float v) ->
      x = DV1.UVALUE_Float v.
  Proof.
    intros x a H.
    induction x;
      repeat red in H; cbn in H;
      repeat break_match_hyp_inv;
      try inv H;
      eauto.
  Qed.

  Lemma uvalue_convert_strict_undef_inv :
    forall x v,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_Undef v) ->
      x = DV1.UVALUE_Undef v.
  Proof.
    intros x a H.
    induction x;
      repeat red in H; cbn in H;
      repeat break_match_hyp_inv;
      try inv H;
      eauto.
  Qed.

  Lemma uvalue_convert_strict_poison_inv :
    forall x v,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_Poison v) ->
      x = DV1.UVALUE_Poison v.
  Proof.
    intros x a H.
    induction x;
      repeat red in H; cbn in H;
      repeat break_match_hyp_inv;
      try inv H;
      eauto.
  Qed.

  Lemma uvalue_convert_strict_oom_inv :
    forall x v,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_Oom v) ->
      x = DV1.UVALUE_Oom v.
  Proof.
    intros x a H.
    induction x;
      repeat red in H; cbn in H;
      repeat break_match_hyp_inv;
      try inv H;
      eauto.
  Qed.

  Lemma uvalue_convert_strict_none_inv :
    forall x,
      uvalue_convert_strict x = NoOom DV2.UVALUE_None ->
      x = DV1.UVALUE_None.
  Proof.
    intros x H.
    induction x;
      repeat red in H; cbn in H;
      repeat break_match_hyp_inv;
      try inv H;
      eauto.
  Qed.

  Lemma uvalue_convert_strict_struct_inv :
    forall x fields,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_Struct fields) ->
      exists fields',
        x = DV1.UVALUE_Struct fields' /\
          map_monad uvalue_convert_strict fields' = NoOom fields.
  Proof.
    intros x a H.
    induction x;
      repeat red in H; cbn in H;
      repeat break_match_hyp_inv;
      try inv H;
      eauto.
  Qed.

  Lemma uvalue_convert_strict_packed_struct_inv :
    forall x fields,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_Packed_struct fields) ->
      exists fields',
        x = DV1.UVALUE_Packed_struct fields' /\
          map_monad uvalue_convert_strict fields' = NoOom fields.
  Proof.
    intros x a H.
    induction x;
      repeat red in H; cbn in H;
      repeat break_match_hyp_inv;
      try inv H;
      eauto.
  Qed.

  Lemma uvalue_convert_strict_array_inv :
    forall x elts t,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_Array t elts) ->
      exists elts',
        x = DV1.UVALUE_Array t elts' /\
          map_monad uvalue_convert_strict elts' = NoOom elts.
  Proof.
    intros x a t H.
    induction x;
      repeat red in H; cbn in H;
      repeat break_match_hyp_inv;
      try inv H;
      eauto.
  Qed.

  Lemma uvalue_convert_strict_vector_inv :
    forall x elts t,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_Vector t elts) ->
      exists elts',
        x = DV1.UVALUE_Vector t elts' /\
          map_monad uvalue_convert_strict elts' = NoOom elts.
  Proof.
    intros x a t H.
    induction x;
      repeat red in H; cbn in H;
      repeat break_match_hyp_inv;
      try inv H;
      eauto.
  Qed.

  Lemma uvalue_convert_strict_ibinop_inv :
    forall x iop uv1 uv2,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_IBinop iop uv1 uv2) ->
      exists uv1' uv2',
        x = DV1.UVALUE_IBinop iop uv1' uv2' /\
          uvalue_convert_strict uv1' = NoOom uv1 /\
          uvalue_convert_strict uv2' = NoOom uv2.
  Proof.
    intros x * H.
    induction x;
      repeat red in H; cbn in H;
      repeat break_match_hyp_inv;
      try inv H;
      eauto.
  Qed.

  Lemma uvalue_convert_strict_icmp_inv :
    forall x icmp uv1 uv2,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_ICmp icmp uv1 uv2) ->
      exists uv1' uv2',
        x = DV1.UVALUE_ICmp icmp uv1' uv2' /\
          uvalue_convert_strict uv1' = NoOom uv1 /\
          uvalue_convert_strict uv2' = NoOom uv2.
  Proof.
    intros x * H.
    induction x;
      repeat red in H; cbn in H;
      repeat break_match_hyp_inv;
      try inv H;
      eauto.
  Qed.

  Lemma uvalue_convert_strict_fbinop_inv :
    forall x fop flags uv1 uv2,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_FBinop fop flags uv1 uv2) ->
      exists uv1' uv2',
        x = DV1.UVALUE_FBinop fop flags uv1' uv2' /\
          uvalue_convert_strict uv1' = NoOom uv1 /\
          uvalue_convert_strict uv2' = NoOom uv2.
  Proof.
    intros x * H.
    induction x;
      repeat red in H; cbn in H;
      repeat break_match_hyp_inv;
      try inv H;
      eauto.
  Qed.

  Lemma uvalue_convert_strict_fcmp_inv :
    forall x fcmp uv1 uv2,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_FCmp fcmp uv1 uv2) ->
      exists uv1' uv2',
        x = DV1.UVALUE_FCmp fcmp uv1' uv2' /\
          uvalue_convert_strict uv1' = NoOom uv1 /\
          uvalue_convert_strict uv2' = NoOom uv2.
  Proof.
    intros x * H.
    induction x;
      repeat red in H; cbn in H;
      repeat break_match_hyp_inv;
      try inv H;
      eauto.
  Qed.

  Lemma uvalue_convert_strict_conversion_inv :
    forall x conv_type dt_from uv dt_to,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_Conversion conv_type dt_from uv dt_to) ->
      exists uv',
        x = DV1.UVALUE_Conversion conv_type dt_from uv' dt_to /\
          uvalue_convert_strict uv' = NoOom uv.
  Proof.
    intros x * H.
    induction x;
      repeat red in H; cbn in H;
      repeat break_match_hyp_inv;
      try inv H;
      eauto.
  Qed.

  Lemma uvalue_convert_strict_gep_inv :
    forall x dt uv_addr uv_idxs,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_GetElementPtr dt uv_addr uv_idxs) ->
      exists uv_addr' uv_idxs',
        x = DV1.UVALUE_GetElementPtr dt uv_addr' uv_idxs' /\
          uvalue_convert_strict uv_addr' = NoOom uv_addr /\
          map_monad uvalue_convert_strict uv_idxs' = NoOom uv_idxs.
  Proof.
    intros x * H.
    induction x;
      repeat red in H; cbn in H;
      repeat break_match_hyp_inv;
      try inv H;
      eauto.
  Qed.

  Lemma uvalue_convert_strict_extract_element_inv :
    forall x dt uv uv_idx,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_ExtractElement dt uv uv_idx) ->
      exists uv' uv_idx',
        x = DV1.UVALUE_ExtractElement dt uv' uv_idx' /\
          uvalue_convert_strict uv' = NoOom uv /\
          uvalue_convert_strict uv_idx' = NoOom uv_idx.
  Proof.
    intros x * H.
    induction x;
      repeat red in H; cbn in H;
      repeat break_match_hyp_inv;
      try inv H;
      eauto.
  Qed.

  Lemma uvalue_convert_strict_insert_element_inv :
    forall x dt uv_vec uv_elt uv_idx,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_InsertElement dt uv_vec uv_elt uv_idx) ->
      exists uv_vec' uv_elt' uv_idx',
        x = DV1.UVALUE_InsertElement dt uv_vec' uv_elt' uv_idx' /\
          uvalue_convert_strict uv_vec' = NoOom uv_vec /\
          uvalue_convert_strict uv_elt' = NoOom uv_elt /\
          uvalue_convert_strict uv_idx' = NoOom uv_idx.
  Proof.
    induction x;
      intros * CONV;
      repeat red in H; cbn in CONV;
      repeat break_match_hyp_inv;
      try inv CONV;
      repeat eexists; eauto.
  Qed.

  Lemma uvalue_convert_strict_shuffle_vector_inv :
    forall x dt vec1 vec2 idxmask,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_ShuffleVector dt vec1 vec2 idxmask) ->
      exists vec1' vec2' idxmask',
        x = DV1.UVALUE_ShuffleVector dt vec1' vec2' idxmask' /\
          uvalue_convert_strict vec1' = NoOom vec1 /\
          uvalue_convert_strict vec2' = NoOom vec2 /\
          uvalue_convert_strict idxmask' = NoOom idxmask.
  Proof.
    induction x;
      intros * CONV;
      repeat red in H; cbn in CONV;
      repeat break_match_hyp_inv;
      try inv CONV;
      repeat eexists; eauto.
  Qed.

  Lemma uvalue_convert_strict_extract_value_inv :
    forall x dt uv idxs,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_ExtractValue dt uv idxs) ->
      exists uv',
        x = DV1.UVALUE_ExtractValue dt uv' idxs /\
          uvalue_convert_strict uv' = NoOom uv.
  Proof.
    induction x;
      intros * CONV;
      repeat red in H; cbn in CONV;
      repeat break_match_hyp_inv;
      try inv CONV;
      repeat eexists; eauto.
  Qed.

  Lemma uvalue_convert_strict_insert_value_inv :
    forall x dt uv dt_elt elt idxs,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_InsertValue dt uv dt_elt elt idxs) ->
      exists uv' elt',
        x = DV1.UVALUE_InsertValue dt uv' dt_elt elt' idxs /\
          uvalue_convert_strict uv' = NoOom uv /\
          uvalue_convert_strict elt' = NoOom elt.
  Proof.
    induction x;
      intros * CONV;
      repeat red in H; cbn in CONV;
      repeat break_match_hyp_inv;
      try inv CONV;
      repeat eexists; eauto.
  Qed.

  Lemma uvalue_convert_strict_select_inv :
    forall x cnd uv1 uv2,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_Select cnd uv1 uv2) ->
      exists cnd' uv1' uv2',
        x = DV1.UVALUE_Select cnd' uv1' uv2' /\
          uvalue_convert_strict cnd' = NoOom cnd /\
          uvalue_convert_strict uv1' = NoOom uv1 /\
          uvalue_convert_strict uv2' = NoOom uv2.
  Proof.
    induction x;
      intros * CONV;
      repeat red in H; cbn in CONV;
      repeat break_match_hyp_inv;
      try inv CONV;
      repeat eexists; eauto.
  Qed.

  Lemma uvalue_convert_strict_extract_byte_inv :
    forall x uv dt idx sid,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_ExtractByte uv dt idx sid) ->
      exists uv',
        x = DV1.UVALUE_ExtractByte uv' dt idx sid /\
          uvalue_convert_strict uv' = NoOom uv.
  Proof.
    induction x;
      intros * CONV;
      repeat red in H; cbn in CONV;
      repeat break_match_hyp_inv;
      try inv CONV;
      repeat eexists; eauto.
  Qed.

  Lemma uvalue_convert_strict_concat_bytes_inv :
    forall x uv_bytes dt,
      uvalue_convert_strict x = NoOom (DV2.UVALUE_ConcatBytes uv_bytes dt) ->
      exists uv_bytes',
        x = DV1.UVALUE_ConcatBytes uv_bytes' dt /\
          map_monad uvalue_convert_strict uv_bytes' = NoOom uv_bytes.
  Proof.
    induction x;
      intros * CONV;
      repeat red in H; cbn in CONV;
      repeat break_match_hyp_inv;
      try inv CONV;
      repeat eexists; eauto.
  Qed.

  Ltac uvalue_convert_strict_inv H :=
    first
      [ apply uvalue_convert_strict_ix_inv in H
      | apply uvalue_convert_strict_iptr_inv in H
      | apply uvalue_convert_strict_addr_inv in H
      | apply uvalue_convert_strict_double_inv in H
      | apply uvalue_convert_strict_float_inv in H
      | apply uvalue_convert_strict_undef_inv in H
      | apply uvalue_convert_strict_poison_inv in H
      | apply uvalue_convert_strict_oom_inv in H
      | apply uvalue_convert_strict_none_inv in H
      | apply uvalue_convert_strict_struct_inv in H
      | apply uvalue_convert_strict_packed_struct_inv in H
      | apply uvalue_convert_strict_array_inv in H
      | apply uvalue_convert_strict_vector_inv in H
      | apply uvalue_convert_strict_ibinop_inv in H
      | apply uvalue_convert_strict_icmp_inv in H
      | apply uvalue_convert_strict_fcmp_inv in H
      | apply uvalue_convert_strict_conversion_inv in H
      | apply uvalue_convert_strict_gep_inv in H
      | apply uvalue_convert_strict_extract_element_inv in H
      | apply uvalue_convert_strict_insert_element_inv in H
      | apply uvalue_convert_strict_shuffle_vector_inv in H
      | apply uvalue_convert_strict_extract_value_inv in H
      | apply uvalue_convert_strict_insert_value_inv in H
      | apply uvalue_convert_strict_select_inv in H
      | apply uvalue_convert_strict_extract_byte_inv in H
      | apply uvalue_convert_strict_concat_bytes_inv in H
      ];
    try first
      [ destruct H as (?&?&?&?&?&?&?)
      | destruct H as (?&?&?&?&?)
      | destruct H as (?&?&?)
      | destruct H as (?&?)]; subst.

  Ltac uvalue_refine_strict_inv H :=
    rewrite uvalue_refine_strict_equation in H;
    uvalue_convert_strict_inv H.

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
  (AC1 : AddrConvert LP1.ADDR LP1.PTOI LP2.ADDR LP2.PTOI) (AC2 : AddrConvert LP2.ADDR LP2.PTOI LP1.ADDR LP1.PTOI)
  (ACSafe : AddrConvertSafe LP1.ADDR LP1.PTOI LP2.ADDR LP2.PTOI AC1 AC2)
  (IPSafe : IPConvertSafe LP1.IP LP2.IP)
  (Events1 : LLVM_INTERACTIONS LP1.ADDR LP1.IP LP1.SIZEOF) (Events2 : LLVM_INTERACTIONS LP2.ADDR LP2.IP LP2.SIZEOF)
  (DVC1 : DVConvert LP1 LP2 AC1 Events1 Events2) (DVC2 : DVConvert LP2 LP1 AC2 Events2 Events1).
  Import ACSafe.
  Import IPSafe.

  (* Lemma Forall2T_InT_r : *)
  (*   forall {A B} (f : A -> B -> Type) (l1 : list A) (l2 : list B), *)
  (*     Forall2T f l1 l2 -> forall b, *)
  (*       InT b l2 -> { a : A & f a b * InT a l1}%type. *)
  (* Proof. *)
  (*   intros A B. *)
  (*   fix IH 4. *)
  (*   intros f l1 l2 H; inversion H; subst; clear H; intros x HX. *)
  (*   - inversion HX. *)
  (*   - inversion HX; subst. *)
  (*     + destruct X as [HF HL]. *)
  (*       exists a. split; auto. left. auto. *)
  (*     + destruct X as [_ HL]. *)
  (*       destruct (IH _ _ _ HL x X0) as [c [HFC HR]]. *)
  (*       exists c. split; auto. right. assumption. *)
  (* Qed. *)

  Lemma dvalue_convert_strict_safe :
    forall dv_f,
      { dv_i : DVC1.DV2.dvalue &
                 ((DVC1.dvalue_convert_strict dv_f = NoOom dv_i) *
                    (DVC2.dvalue_convert_strict dv_i = NoOom dv_f))%type}.
  Proof.
    intros dv_f.
    induction dv_f;
      try solve [ cbn;
                  eexists;
                  cbn;
                  split; eauto ].
    - (* Addresses *)
      cbn.
      pose proof (ACSafe.addr_convert_succeeds a) as [a2 ACSUC].
      cbn.
      exists (DVC1.DV2.DVALUE_Addr a2).
      rewrite ACSUC.
      cbn.
      rewrite (ACSafe.addr_convert_safe a); auto.
    - (* Intptr expressions... *)
      cbn.
      pose proof (intptr_convert_succeeds x) as [y IPSUC].
      cbn.
      exists (DVC1.DV2.DVALUE_IPTR y).
      rewrite IPSUC.
      cbn.
      rewrite (IPSafe.intptr_convert_safe x); auto.
    - (* Structures *)
      cbn.
      break_match_goal.
      + eexists; split; [reflexivity|].
        cbn.
        break_match_goal.
        apply map_monad_oom_Forall2T in Heqo.
        apply map_monad_oom_Forall2T in Heqo0.
        * assert (l0 = fields).
           { revert fields l Heqo X l0 Heqo0.
             fix IH 3.  (* This is a bit unsatifsactory *)
             intros.
             inversion Heqo; clear Heqo; subst.
             -- inversion Heqo0.
                reflexivity.
             -- inversion Heqo0; clear Heqo0; subst.
                destruct H as [HD1 IH1].
                destruct H3 as [HD2 IH2].
                assert (InT a (a::l1)) by (left; auto).
                destruct (X _ X0) as [dv2 [EQ1 EQ2]].

                specialize (DVC1.dvalue_refine_strict_R2_injective _ _ _ _ HD1 EQ1) as [EQA EQB].
                specialize (DVC2.dvalue_refine_strict_R2_injective _ _ _ _ HD2 EQ2) as [EQC EQD].
                rewrite EQC; auto.
                clear b HD1 HD2 X0 dv2 EQ1 EQ2 EQA EQB EQC EQD X0 HD2 EQ2.
                forward (IH _ _ IH1).
                intros. apply X. right.  assumption.
                apply IH in IH2. rewrite IH2.
                reflexivity.
           }
           rewrite H. reflexivity.
        * apply map_monad_oom_Forall2T in Heqo.
          rewrite map_monad_map_monad_InT in Heqo0.
          apply map_monad_InT_OOM_fail in Heqo0.
          destruct Heqo0 as [a [IN CONVa]].
          destruct (Forall2T_InT_r _ _ _ Heqo _ IN).
          destruct p as [EQx INx].
          destruct (X x INx).
          destruct p as [EQx' EQx0].
          specialize (DVC1.dvalue_refine_strict_R2_injective _ _ _ _ EQx EQx') as [EQA EQB].
          rewrite EQA in *; auto.
          rewrite CONVa in EQx0.
          inversion EQx0.
      + rewrite map_monad_map_monad_InT in Heqo.
        apply map_monad_InT_OOM_fail in Heqo.
        exists DVC1.DV2.DVALUE_None. split.
        * destruct Heqo as [a [IN CONVa]].
          destruct (X a IN).
          destruct p as [EQx' EQx0].
          rewrite CONVa in EQx'.
          inversion EQx'.
        * destruct Heqo as [a [IN CONVa]].
          destruct (X a IN).
          destruct p as [EQx' EQx0].
          rewrite CONVa in EQx'.
          inversion EQx'.

    - (* Structures *)
      cbn.
      break_match_goal.
      + eexists; split; [reflexivity|].
        cbn.
        break_match_goal.
        apply map_monad_oom_Forall2T in Heqo.
        apply map_monad_oom_Forall2T in Heqo0.
        * assert (l0 = fields).
           { revert fields l Heqo X l0 Heqo0.
             fix IH 3.  (* This is a bit unsatifsactory *)
             intros.
             inversion Heqo; clear Heqo; subst.
             -- inversion Heqo0.
                reflexivity.
             -- inversion Heqo0; clear Heqo0; subst.
                destruct H as [HD1 IH1].
                destruct H3 as [HD2 IH2].
                assert (InT a (a::l1)) by (left; auto).
                destruct (X _ X0) as [dv2 [EQ1 EQ2]].

                specialize (DVC1.dvalue_refine_strict_R2_injective _ _ _ _ HD1 EQ1) as [EQA EQB].
                specialize (DVC2.dvalue_refine_strict_R2_injective _ _ _ _ HD2 EQ2) as [EQC EQD].
                rewrite EQC; auto.
                clear b HD1 HD2 X0 dv2 EQ1 EQ2 EQA EQB EQC EQD X0 HD2 EQ2.
                forward (IH _ _ IH1).
                intros. apply X. right.  assumption.
                apply IH in IH2. rewrite IH2.
                reflexivity.
           }
           rewrite H. reflexivity.
        * apply map_monad_oom_Forall2T in Heqo.
          rewrite map_monad_map_monad_InT in Heqo0.
          apply map_monad_InT_OOM_fail in Heqo0.
          destruct Heqo0 as [a [IN CONVa]].
          destruct (Forall2T_InT_r _ _ _ Heqo _ IN).
          destruct p as [EQx INx].
          destruct (X x INx).
          destruct p as [EQx' EQx0].
          specialize (DVC1.dvalue_refine_strict_R2_injective _ _ _ _ EQx EQx') as [EQA EQB].
          rewrite EQA in *; auto.
          rewrite CONVa in EQx0.
          inversion EQx0.
      + rewrite map_monad_map_monad_InT in Heqo.
        apply map_monad_InT_OOM_fail in Heqo.
        exists DVC1.DV2.DVALUE_None. split.
        * destruct Heqo as [a [IN CONVa]].
          destruct (X a IN).
          destruct p as [EQx' EQx0].
          rewrite CONVa in EQx'.
          inversion EQx'.
        * destruct Heqo as [a [IN CONVa]].
          destruct (X a IN).
          destruct p as [EQx' EQx0].
          rewrite CONVa in EQx'.
          inversion EQx'.

    - (* Array *)
      cbn.
      break_match_goal.
      + eexists; split; [reflexivity|].
        cbn.
        break_match_goal.
        apply map_monad_oom_Forall2T in Heqo.
        apply map_monad_oom_Forall2T in Heqo0.
        * assert (l0 = elts).
           { revert elts l Heqo X l0 Heqo0.
             fix IH 3.  (* This is a bit unsatifsactory *)
             intros.
             inversion Heqo; clear Heqo; subst.
             -- inversion Heqo0.
                reflexivity.
             -- inversion Heqo0; clear Heqo0; subst.
                destruct H as [HD1 IH1].
                destruct H3 as [HD2 IH2].
                assert (InT a (a::l1)) by (left; auto).
                destruct (X _ X0) as [dv2 [EQ1 EQ2]].

                specialize (DVC1.dvalue_refine_strict_R2_injective _ _ _ _ HD1 EQ1) as [EQA EQB].
                specialize (DVC2.dvalue_refine_strict_R2_injective _ _ _ _ HD2 EQ2) as [EQC EQD].
                rewrite EQC; auto.
                clear b HD1 HD2 X0 dv2 EQ1 EQ2 EQA EQB EQC EQD X0 HD2 EQ2.
                forward (IH _ _ IH1).
                intros. apply X. right.  assumption.
                apply IH in IH2. rewrite IH2.
                reflexivity.
           }
           rewrite H. reflexivity.

        * apply map_monad_oom_Forall2T in Heqo.
          rewrite map_monad_map_monad_InT in Heqo0.
          apply map_monad_InT_OOM_fail in Heqo0.
          destruct Heqo0 as [a [IN CONVa]].
          destruct (Forall2T_InT_r _ _ _ Heqo _ IN).
          destruct p as [EQx INx].
          destruct (X x INx).
          destruct p as [EQx' EQx0].
          specialize (DVC1.dvalue_refine_strict_R2_injective _ _ _ _ EQx EQx') as [EQA EQB].
          rewrite EQA in *; auto.
          rewrite CONVa in EQx0.
          inversion EQx0.
      + rewrite map_monad_map_monad_InT in Heqo.
        apply map_monad_InT_OOM_fail in Heqo.
        exists DVC1.DV2.DVALUE_None. split.
        * destruct Heqo as [a [IN CONVa]].
          destruct (X a IN).
          destruct p as [EQx' EQx0].
          rewrite CONVa in EQx'.
          inversion EQx'.
        * destruct Heqo as [a [IN CONVa]].
          destruct (X a IN).
          destruct p as [EQx' EQx0].
          rewrite CONVa in EQx'.
          inversion EQx'.

   - (* Vector *)
      cbn.
      break_match_goal.
      + eexists; split; [reflexivity|].
        cbn.
        break_match_goal.
        apply map_monad_oom_Forall2T in Heqo.
        apply map_monad_oom_Forall2T in Heqo0.
        * assert (l0 = elts).
           { revert elts l Heqo X l0 Heqo0.
             fix IH 3.  (* This is a bit unsatifsactory *)
             intros.
             inversion Heqo; clear Heqo; subst.
             -- inversion Heqo0.
                reflexivity.
             -- inversion Heqo0; clear Heqo0; subst.
                destruct H as [HD1 IH1].
                destruct H3 as [HD2 IH2].
                assert (InT a (a::l1)) by (left; auto).
                destruct (X _ X0) as [dv2 [EQ1 EQ2]].

                specialize (DVC1.dvalue_refine_strict_R2_injective _ _ _ _ HD1 EQ1) as [EQA EQB].
                specialize (DVC2.dvalue_refine_strict_R2_injective _ _ _ _ HD2 EQ2) as [EQC EQD].
                rewrite EQC; auto.
                clear b HD1 HD2 X0 dv2 EQ1 EQ2 EQA EQB EQC EQD X0 HD2 EQ2.
                forward (IH _ _ IH1).
                intros. apply X. right.  assumption.
                apply IH in IH2. rewrite IH2.
                reflexivity.
           }
           rewrite H. reflexivity.

        * apply map_monad_oom_Forall2T in Heqo.
          rewrite map_monad_map_monad_InT in Heqo0.
          apply map_monad_InT_OOM_fail in Heqo0.
          destruct Heqo0 as [a [IN CONVa]].
          destruct (Forall2T_InT_r _ _ _ Heqo _ IN).
          destruct p as [EQx INx].
          destruct (X x INx).
          destruct p as [EQx' EQx0].
          specialize (DVC1.dvalue_refine_strict_R2_injective _ _ _ _ EQx EQx') as [EQA EQB].
          rewrite EQA in *; auto.
          rewrite CONVa in EQx0.
          inversion EQx0.
      + rewrite map_monad_map_monad_InT in Heqo.
        apply map_monad_InT_OOM_fail in Heqo.
        exists DVC1.DV2.DVALUE_None. split.
        * destruct Heqo as [a [IN CONVa]].
          destruct (X a IN).
          destruct p as [EQx' EQx0].
          rewrite CONVa in EQx'.
          inversion EQx'.
        * destruct Heqo as [a [IN CONVa]].
          destruct (X a IN).
          destruct p as [EQx' EQx0].
          rewrite CONVa in EQx'.
          inversion EQx'.
  Qed.

  Lemma uvalue_convert_strict_safe :
    forall uv_f,
      { uv_i : DVC1.DV2.uvalue &
                 ((DVC1.uvalue_convert_strict uv_f = NoOom uv_i) *
                    (DVC2.uvalue_convert_strict uv_i = NoOom uv_f))%type}.
  Proof.
    intros uv_f.
    induction uv_f;
      try solve [
          cbn; eexists; cbn; split; eauto
        | destruct IHuv_f1 as [uv_i1 [UVfi1 UVif1]];
          destruct IHuv_f2 as [uv_i2 [UVfi2 UVif2]];
          cbn;
          rewrite UVfi1, UVfi2;
          cbn;
          eexists; split; eauto;
          cbn;
          rewrite UVif1, UVif2;
          cbn; eauto
        | destruct IHuv_f1 as [uv_i1 [UVfi1 UVif1]];
          destruct IHuv_f2 as [uv_i2 [UVfi2 UVif2]];
          destruct IHuv_f3 as [uv_i3 [UVfi3 UVif3]];
          cbn;
          rewrite UVfi1, UVfi2, UVfi3;
          cbn;
          eexists; split; eauto;
          cbn;
            rewrite UVif1, UVif2, UVif3;
            cbn; eauto
        | destruct IHuv_f as [uv_i [UVfi UVif]];
          cbn;
          rewrite UVfi;
          cbn;
          eexists; split; eauto;
          cbn;
          rewrite UVif;
          cbn; eauto
        ].

    - (* Addresses *)
      cbn.
      pose proof (ACSafe.addr_convert_succeeds a) as [a2 ACSUC].
      rewrite ACSUC.
      exists (DVC1.DV2.UVALUE_Addr a2).
      cbn.
      rewrite (ACSafe.addr_convert_safe a); auto.
    - (* Intptr expressions... *)
      cbn.
      pose proof (intptr_convert_succeeds x) as [y IPSUC].
      rewrite IPSUC.
      exists (DVC1.DV2.UVALUE_IPTR y).
      cbn.
      rewrite (IPSafe.intptr_convert_safe x); auto.

    - (* Structures *)
      cbn.
      break_match_goal.
      + eexists; split; [reflexivity|].
        cbn.
        break_match_goal.
        apply map_monad_oom_Forall2T in Heqo.
        apply map_monad_oom_Forall2T in Heqo0.
        * assert (l0 = fields).
           { revert fields l Heqo X l0 Heqo0.
             fix IH 3.  (* This is a bit unsatifsactory *)
             intros.
             inversion Heqo; clear Heqo; subst.
             -- inversion Heqo0.
                reflexivity.
             -- inversion Heqo0; clear Heqo0; subst.
                destruct H as [HD1 IH1].
                destruct H3 as [HD2 IH2].
                assert (InT a (a::l1)) by (left; auto).
                destruct (X _ X0) as [dv2 [EQ1 EQ2]].

                specialize (DVC1.uvalue_refine_strict_R2_injective _ _ _ _ HD1 EQ1) as [EQA EQB].
                specialize (DVC2.uvalue_refine_strict_R2_injective _ _ _ _ HD2 EQ2) as [EQC EQD].
                rewrite EQC; auto.
                clear b HD1 HD2 X0 dv2 EQ1 EQ2 EQA EQB EQC EQD X0 HD2 EQ2.
                forward (IH _ _ IH1).
                intros. apply X. right.  assumption.
                apply IH in IH2. rewrite IH2.
                reflexivity.
           }
           rewrite H. reflexivity.
        * apply map_monad_oom_Forall2T in Heqo.
          rewrite map_monad_map_monad_InT in Heqo0.
          apply map_monad_InT_OOM_fail in Heqo0.
          destruct Heqo0 as [a [IN CONVa]].
          destruct (Forall2T_InT_r _ _ _ Heqo _ IN).
          destruct p as [EQx INx].
          destruct (X x INx).
          destruct p as [EQx' EQx0].
          specialize (DVC1.uvalue_refine_strict_R2_injective _ _ _ _ EQx EQx') as [EQA EQB].
          rewrite EQA in *; auto.
          rewrite CONVa in EQx0.
          inversion EQx0.
      + rewrite map_monad_map_monad_InT in Heqo.
        apply map_monad_InT_OOM_fail in Heqo.
        exists DVC1.DV2.UVALUE_None. split.
        * destruct Heqo as [a [IN CONVa]].
          destruct (X a IN).
          destruct p as [EQx' EQx0].
          rewrite CONVa in EQx'.
          inversion EQx'.
        * destruct Heqo as [a [IN CONVa]].
          destruct (X a IN).
          destruct p as [EQx' EQx0].
          rewrite CONVa in EQx'.
          inversion EQx'.

    - (* Structures *)
      cbn.
      break_match_goal.
      + eexists; split; [reflexivity|].
        cbn.
        break_match_goal.
        apply map_monad_oom_Forall2T in Heqo.
        apply map_monad_oom_Forall2T in Heqo0.
        * assert (l0 = fields).
           { revert fields l Heqo X l0 Heqo0.
             fix IH 3.  (* This is a bit unsatifsactory *)
             intros.
             inversion Heqo; clear Heqo; subst.
             -- inversion Heqo0.
                reflexivity.
             -- inversion Heqo0; clear Heqo0; subst.
                destruct H as [HD1 IH1].
                destruct H3 as [HD2 IH2].
                assert (InT a (a::l1)) by (left; auto).
                destruct (X _ X0) as [dv2 [EQ1 EQ2]].

                specialize (DVC1.uvalue_refine_strict_R2_injective _ _ _ _ HD1 EQ1) as [EQA EQB].
                specialize (DVC2.uvalue_refine_strict_R2_injective _ _ _ _ HD2 EQ2) as [EQC EQD].
                rewrite EQC; auto.
                clear b HD1 HD2 X0 dv2 EQ1 EQ2 EQA EQB EQC EQD X0 HD2 EQ2.
                forward (IH _ _ IH1).
                intros. apply X. right.  assumption.
                apply IH in IH2. rewrite IH2.
                reflexivity.
           }
           rewrite H. reflexivity.
        * apply map_monad_oom_Forall2T in Heqo.
          rewrite map_monad_map_monad_InT in Heqo0.
          apply map_monad_InT_OOM_fail in Heqo0.
          destruct Heqo0 as [a [IN CONVa]].
          destruct (Forall2T_InT_r _ _ _ Heqo _ IN).
          destruct p as [EQx INx].
          destruct (X x INx).
          destruct p as [EQx' EQx0].
          specialize (DVC1.uvalue_refine_strict_R2_injective _ _ _ _ EQx EQx') as [EQA EQB].
          rewrite EQA in *; auto.
          rewrite CONVa in EQx0.
          inversion EQx0.
      + rewrite map_monad_map_monad_InT in Heqo.
        apply map_monad_InT_OOM_fail in Heqo.
        exists DVC1.DV2.UVALUE_None. split.
        * destruct Heqo as [a [IN CONVa]].
          destruct (X a IN).
          destruct p as [EQx' EQx0].
          rewrite CONVa in EQx'.
          inversion EQx'.
        * destruct Heqo as [a [IN CONVa]].
          destruct (X a IN).
          destruct p as [EQx' EQx0].
          rewrite CONVa in EQx'.
          inversion EQx'.

    - (* Array *)
      cbn.
      break_match_goal.
      + eexists; split; [reflexivity|].
        cbn.
        break_match_goal.
        apply map_monad_oom_Forall2T in Heqo.
        apply map_monad_oom_Forall2T in Heqo0.
        * assert (l0 = elts).
           { revert elts l Heqo X l0 Heqo0.
             fix IH 3.  (* This is a bit unsatifsactory *)
             intros.
             inversion Heqo; clear Heqo; subst.
             -- inversion Heqo0.
                reflexivity.
             -- inversion Heqo0; clear Heqo0; subst.
                destruct H as [HD1 IH1].
                destruct H3 as [HD2 IH2].
                assert (InT a (a::l1)) by (left; auto).
                destruct (X _ X0) as [dv2 [EQ1 EQ2]].

                specialize (DVC1.uvalue_refine_strict_R2_injective _ _ _ _ HD1 EQ1) as [EQA EQB].
                specialize (DVC2.uvalue_refine_strict_R2_injective _ _ _ _ HD2 EQ2) as [EQC EQD].
                rewrite EQC; auto.
                clear b HD1 HD2 X0 dv2 EQ1 EQ2 EQA EQB EQC EQD X0 HD2 EQ2.
                forward (IH _ _ IH1).
                intros. apply X. right.  assumption.
                apply IH in IH2. rewrite IH2.
                reflexivity.
           }
           rewrite H. reflexivity.

        * apply map_monad_oom_Forall2T in Heqo.
          rewrite map_monad_map_monad_InT in Heqo0.
          apply map_monad_InT_OOM_fail in Heqo0.
          destruct Heqo0 as [a [IN CONVa]].
          destruct (Forall2T_InT_r _ _ _ Heqo _ IN).
          destruct p as [EQx INx].
          destruct (X x INx).
          destruct p as [EQx' EQx0].
          specialize (DVC1.uvalue_refine_strict_R2_injective _ _ _ _ EQx EQx') as [EQA EQB].
          rewrite EQA in *; auto.
          rewrite CONVa in EQx0.
          inversion EQx0.
      + rewrite map_monad_map_monad_InT in Heqo.
        apply map_monad_InT_OOM_fail in Heqo.
        exists DVC1.DV2.UVALUE_None. split.
        * destruct Heqo as [a [IN CONVa]].
          destruct (X a IN).
          destruct p as [EQx' EQx0].
          rewrite CONVa in EQx'.
          inversion EQx'.
        * destruct Heqo as [a [IN CONVa]].
          destruct (X a IN).
          destruct p as [EQx' EQx0].
          rewrite CONVa in EQx'.
          inversion EQx'.


    - (* Vector *)
      cbn.
      break_match_goal.
      + eexists; split; [reflexivity|].
        cbn.
        break_match_goal.
        apply map_monad_oom_Forall2T in Heqo.
        apply map_monad_oom_Forall2T in Heqo0.
        * assert (l0 = elts).
           { revert elts l Heqo X l0 Heqo0.
             fix IH 3.  (* This is a bit unsatifsactory *)
             intros.
             inversion Heqo; clear Heqo; subst.
             -- inversion Heqo0.
                reflexivity.
             -- inversion Heqo0; clear Heqo0; subst.
                destruct H as [HD1 IH1].
                destruct H3 as [HD2 IH2].
                assert (InT a (a::l1)) by (left; auto).
                destruct (X _ X0) as [dv2 [EQ1 EQ2]].

                specialize (DVC1.uvalue_refine_strict_R2_injective _ _ _ _ HD1 EQ1) as [EQA EQB].
                specialize (DVC2.uvalue_refine_strict_R2_injective _ _ _ _ HD2 EQ2) as [EQC EQD].
                rewrite EQC; auto.
                clear b HD1 HD2 X0 dv2 EQ1 EQ2 EQA EQB EQC EQD X0 HD2 EQ2.
                forward (IH _ _ IH1).
                intros. apply X. right.  assumption.
                apply IH in IH2. rewrite IH2.
                reflexivity.
           }
           rewrite H. reflexivity.

        * apply map_monad_oom_Forall2T in Heqo.
          rewrite map_monad_map_monad_InT in Heqo0.
          apply map_monad_InT_OOM_fail in Heqo0.
          destruct Heqo0 as [a [IN CONVa]].
          destruct (Forall2T_InT_r _ _ _ Heqo _ IN).
          destruct p as [EQx INx].
          destruct (X x INx).
          destruct p as [EQx' EQx0].
          specialize (DVC1.uvalue_refine_strict_R2_injective _ _ _ _ EQx EQx') as [EQA EQB].
          rewrite EQA in *; auto.
          rewrite CONVa in EQx0.
          inversion EQx0.
      + rewrite map_monad_map_monad_InT in Heqo.
        apply map_monad_InT_OOM_fail in Heqo.
        exists DVC1.DV2.UVALUE_None. split.
        * destruct Heqo as [a [IN CONVa]].
          destruct (X a IN).
          destruct p as [EQx' EQx0].
          rewrite CONVa in EQx'.
          inversion EQx'.
        * destruct Heqo as [a [IN CONVa]].
          destruct (X a IN).
          destruct p as [EQx' EQx0].
          rewrite CONVa in EQx'.
          inversion EQx'.

    - (* GEP *)
      cbn.
      repeat break_match_goal.
      + eexists; split; [reflexivity|].
        cbn.
        repeat break_match_goal.
        * destruct IHuv_f as [f [HF1 HF2]].
          inversion HF1; subst.
          rewrite HF2 in Heqo1. inversion Heqo1; subst.
          clear f HF2  Heqo1 HF1 Heqo.

          apply map_monad_oom_Forall2T in Heqo0.
          apply map_monad_oom_Forall2T in Heqo2.
          assert (l0 = idxs).
           { revert idxs l Heqo0 X l0 Heqo2.
             fix IH 3.  (* This is a bit unsatifsactory *)
             intros.
             inversion Heqo0; clear Heqo0; subst.
             -- inversion Heqo2.
                reflexivity.
             -- inversion Heqo2; clear Heqo2; subst.
                destruct H as [HD1 IH1].
                destruct H3 as [HD2 IH2].
                assert (InT a (a::l1)) by (left; auto).
                destruct (X _ X0) as [dv2 [EQ1 EQ2]].

                specialize (DVC1.uvalue_refine_strict_R2_injective _ _ _ _ HD1 EQ1) as [EQA EQB].
                specialize (DVC2.uvalue_refine_strict_R2_injective _ _ _ _ HD2 EQ2) as [EQC EQD].
                rewrite EQC; auto.
                clear b HD1 HD2 X0 dv2 EQ1 EQ2 EQA EQB EQC EQD X0 HD2 EQ2.
                forward (IH _ _ IH1).
                intros. apply X. right.  assumption.
                apply IH in IH2. rewrite IH2.
                reflexivity.
           }
           rewrite H. reflexivity.
        * apply map_monad_oom_Forall2T in Heqo0.
          rewrite map_monad_map_monad_InT in Heqo2.
          apply map_monad_InT_OOM_fail in Heqo2.
          destruct Heqo2 as [a [IN CONVa]].
          destruct (Forall2T_InT_r _ _ _ Heqo0 _ IN).
          destruct p as [EQx INx].
          destruct (X x INx).
          destruct p as [EQx' EQx0].
          specialize (DVC1.uvalue_refine_strict_R2_injective _ _ _ _ EQx EQx') as [EQA EQB].
          rewrite EQA in *; auto.
          rewrite CONVa in EQx0.
          inversion EQx0.
        * destruct IHuv_f as [f [EQF1 EQF2]].
          inversion EQF1; subst.
          rewrite EQF2 in Heqo1.
          inversion Heqo1.

      + rewrite map_monad_map_monad_InT in Heqo0.
        apply map_monad_InT_OOM_fail in Heqo0.
        exists DVC1.DV2.UVALUE_None. split.
        * destruct Heqo0 as [a [IN CONVa]].
          destruct (X a IN).
          destruct p as [EQx' EQx0].
          rewrite CONVa in EQx'.
          inversion EQx'.
        * destruct Heqo0 as [a [IN CONVa]].
          destruct (X a IN).
          destruct p as [EQx' EQx0].
          rewrite CONVa in EQx'.
          inversion EQx'.
      + destruct IHuv_f as [f [EQF1 _]].
        inversion EQF1.

    - (* Vector *)
      cbn.
      break_match_goal.
      + eexists; split; [reflexivity|].
        cbn.
        break_match_goal.
        apply map_monad_oom_Forall2T in Heqo.
        apply map_monad_oom_Forall2T in Heqo0.
        * assert (uvs = l0).
           { revert uvs l Heqo X l0 Heqo0.
             fix IH 3.  (* This is a bit unsatifsactory *)
             intros.
             inversion Heqo; clear Heqo; subst.
             -- inversion Heqo0.
                reflexivity.
             -- inversion Heqo0; clear Heqo0; subst.
                destruct H as [HD1 IH1].
                destruct H3 as [HD2 IH2].
                assert (InT a (a::l1)) by (left; auto).
                destruct (X _ X0) as [dv2 [EQ1 EQ2]].

                specialize (DVC1.uvalue_refine_strict_R2_injective _ _ _ _ HD1 EQ1) as [EQA EQB].
                specialize (DVC2.uvalue_refine_strict_R2_injective _ _ _ _ HD2 EQ2) as [EQC EQD].
                rewrite EQC; auto.
                clear b HD1 HD2 X0 dv2 EQ1 EQ2 EQA EQB EQC EQD X0 HD2 EQ2.
                forward (IH _ _ IH1).
                intros. apply X. right.  assumption.
                apply IH in IH2. rewrite IH2.
                reflexivity.
           }
           rewrite H. reflexivity.

        * apply map_monad_oom_Forall2T in Heqo.
          rewrite map_monad_map_monad_InT in Heqo0.
          apply map_monad_InT_OOM_fail in Heqo0.
          destruct Heqo0 as [a [IN CONVa]].
          destruct (Forall2T_InT_r _ _ _ Heqo _ IN).
          destruct p as [EQx INx].
          destruct (X x INx).
          destruct p as [EQx' EQx0].
          specialize (DVC1.uvalue_refine_strict_R2_injective _ _ _ _ EQx EQx') as [EQA EQB].
          rewrite EQA in *; auto.
          rewrite CONVa in EQx0.
          inversion EQx0.
      + rewrite map_monad_map_monad_InT in Heqo.
        apply map_monad_InT_OOM_fail in Heqo.
        exists DVC1.DV2.UVALUE_None. split.
        * destruct Heqo as [a [IN CONVa]].
          destruct (X a IN).
          destruct p as [EQx' EQx0].
          rewrite CONVa in EQx'.
          inversion EQx'.
        * destruct Heqo as [a [IN CONVa]].
          destruct (X a IN).
          destruct p as [EQx' EQx0].
          rewrite CONVa in EQx'.
          inversion EQx'.
  Qed.

End DVConvertSafe.
