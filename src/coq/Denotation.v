(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

From Coq Require Import
     ZArith String List
     FSets.FMapWeakList
     Bool.Bool.

Require Import Integers Floats.

From ExtLib Require Import
     Programming.Show
     Structures.Monads
     Structures.Functor
     Eqv.

From ITree Require Import
     ITree
     Interp.Recursion
     Events.Exception.

From Vellvm Require Import
     Util
     Error
     LLVMAst
     AstLib
     CFG
     DynamicTypes
     MemoryAddress
     LLVMEvents
     TypeUtil
     Handlers.Intrinsics.

(* YZ: Undesirable dependency on Handlers/Intrinsics: move [intrinsic_exp] somewhere else? *)

Import Sum.
Import Subevent.
Import EqvNotation.
Import ListNotations.
Import MonadNotation.
Import ShowNotation.

Set Implicit Arguments.
Set Contextual Implicit.

Open Scope monad_scope.
Open Scope string_scope.
Open Scope Z_scope.


(* YZ Ask Steve: why is LLVMEvents an argument to the functor rather than have Make(A) inside the module? *)
Module Denotation(A:MemoryAddress.ADDRESS)(LLVMEvents:LLVM_INTERACTIONS(A)).

  Import LLVMEvents.
  (* Denotational semantics of LLVM programs.
     Each sub-component is denoted as an itree that can emit any of the following effects:
     - Internal Call (CallE)
     - External Call (IntrinsicE and MemoryIntrinsicE)
     - Manipulation of the local environment (LocalE)
     - Memory interactions (MemoryE)
     - Failure (FailureE)
     - Emit debugging information (DebugE)
   *)

  (* Maybe should be "Locals +' CallE +' blah ...."

     If you handle locals before you tie the knot, then you basically
     have a single environment. Then calls need to handle stack.


     (itree (CallE +' Locals +' CallE +' IO +' failureE +' debugE)).

     Pure intrinsics, like math. Sin / cos and stuff. Some need to be
     handled at the memory model level, like memcpy.

     Do we need to separate ExternalCalls? Or Memory model
     takes... CallE +' IO and produces CallE
     itrees. Handles some ExternalCalls, but not necessarily all of
     them.

     Rename IO to MemE or something.

     (itree (CallE +' Locals +' CallE +' IO +' failureE +' debugE)).

     - Denotation: gets rid of CallE denote_mcfg (denote_cfg in practice never emits ExternalCalls)
       + Linking, do we want to make this distinction?
     - LocalEnvironment: gets rid of locals
     - Intrinsics.v: should this be two?
     - Memory.v: takes CallE and IO


     - Add MemoryIntrinsic to IO, kind of like how Call used to be. Can now interpret away entirely inside memory model
       + Call would have to figure out which ones are memory
         intrinsics and which ones are not. Should have this information
         while linking CFGs.
       + General memory models need a way of registering which intrinsics they handle.
  *)

  (* The mutually recursive functions are tied together, interpreting away all internal calls*)

  Section CONVERSIONS.
    (* Conversions can't go into DynamicValues because Int2Ptr and Ptr2Int casts
       generate memory effects. *)
    (* SAZ: for some reason, typeclass resolution was taking forever in eval_conv_h,
        so I respecialized it... *)
    Definition spec_raise {X} (s:string) : itree L0 X := raise s.

    (* YZ: Inferring the subevent instance takes a small but non-trivial amount of time,
       and has to be done here hundreds and hundreds of times. Factoring the inferrence is crucial.
     *)
    Definition eval_conv_h conv (t1:dtyp) (x:dvalue) (t2:dtyp) : itree conv_E dvalue :=
      let raise := @raise conv_E dvalue _
      in
      match conv with
      | Trunc =>
        match t1, x, t2 with
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 1 =>
          ret (DVALUE_I1 (repr (unsigned i1)))
        | DTYPE_I 8, DVALUE_Poison, DTYPE_I 1 =>
          ret DVALUE_Poison
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 1 =>
          ret (DVALUE_I1 (repr (unsigned i1)))
        | DTYPE_I 32, DVALUE_Poison, DTYPE_I 1 =>
          ret DVALUE_Poison
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 8 =>
          ret (DVALUE_I8 (repr (unsigned i1)))
        | DTYPE_I 32, DVALUE_Poison, DTYPE_I 8 =>
          ret DVALUE_Poison
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_I 1 =>
          ret (DVALUE_I1 (repr (unsigned i1)))
        | DTYPE_I 64, DVALUE_Poison, DTYPE_I 1 =>
          ret DVALUE_Poison
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_I 8 =>
          ret (DVALUE_I8 (repr (unsigned i1)))
        | DTYPE_I 64, DVALUE_Poison, DTYPE_I 8 =>
          ret DVALUE_Poison
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_I 32 =>
          ret (DVALUE_I32 (repr (unsigned i1)))
        | DTYPE_I 64, DVALUE_Poison, DTYPE_I 32 =>
          ret DVALUE_Poison
        | _, _, _ => raise "ill typed-conv"
        end
      | Zext =>
        match t1, x, t2 with
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 8 =>
          ret (DVALUE_I8 (repr (unsigned i1)))
        | DTYPE_I 1, DVALUE_Poison, DTYPE_I 8 =>
          ret DVALUE_Poison
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 32 =>
          ret (DVALUE_I32 (repr (unsigned i1)))
        | DTYPE_I 1, DVALUE_Poison, DTYPE_I 32 =>
          ret DVALUE_Poison
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 64 =>
          ret (DVALUE_I64 (repr (unsigned i1)))
        | DTYPE_I 1, DVALUE_Poison, DTYPE_I 64 =>
          ret DVALUE_Poison
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 32 =>
          ret (DVALUE_I32 (repr (unsigned i1)))
        | DTYPE_I 8, DVALUE_Poison, DTYPE_I 32 =>
          ret DVALUE_Poison
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 64 =>
          ret (DVALUE_I64 (repr (unsigned i1)))
        | DTYPE_I 8, DVALUE_Poison, DTYPE_I 64 =>
          ret DVALUE_Poison
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 64 =>
          ret (DVALUE_I64 (repr (unsigned i1)))
        | DTYPE_I 32, DVALUE_Poison, DTYPE_I 64 =>
          ret DVALUE_Poison
        | _, _, _ => raise "ill typed-conv"
        end
      | Sext =>
        match t1, x, t2 with
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 8 =>
          ret (DVALUE_I8 (repr (signed i1)))
        | DTYPE_I 1, DVALUE_Poison, DTYPE_I 8 =>
          ret DVALUE_Poison
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 32 =>
          ret (DVALUE_I32 (repr (signed i1)))
        | DTYPE_I 1, DVALUE_Poison, DTYPE_I 32 =>
          ret DVALUE_Poison
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 64 =>
          ret (DVALUE_I64 (repr (signed i1)))
        | DTYPE_I 1, DVALUE_Poison, DTYPE_I 64 =>
          ret DVALUE_Poison
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 32 =>
          ret (DVALUE_I32 (repr (signed i1)))
        | DTYPE_I 8, DVALUE_Poison, DTYPE_I 32 =>
          ret DVALUE_Poison
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 64 =>
          ret (DVALUE_I64 (repr (signed i1)))
        | DTYPE_I 8, DVALUE_Poison, DTYPE_I 64 =>
          ret DVALUE_Poison
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 64 =>
          ret (DVALUE_I64 (repr (signed i1)))
        | DTYPE_I 32, DVALUE_Poison, DTYPE_I 64 =>
          ret DVALUE_Poison
        | _, _, _ => raise "ill typed-conv"
        end
      | Bitcast =>
        match t1, x, t2 with
        | DTYPE_I bits1, x, DTYPE_I bits2 =>
          if bits1 =? bits2 then ret x else raise "unequal bitsize in cast"
        | DTYPE_Pointer, DVALUE_Addr a, DTYPE_Pointer =>
          ret (DVALUE_Addr a)
        | DTYPE_Pointer, DVALUE_Poison, DTYPE_Pointer =>
          ret DVALUE_Poison
        | _, _, _ => raise "ill-typed_conv"
        end
      | Uitofp =>
        match t1, x, t2 with
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Float =>
          ret (DVALUE_Float (Float32.of_intu (repr (unsigned i1))))
        | DTYPE_I 1, DVALUE_Poison, DTYPE_Float =>
          ret DVALUE_Poison

        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Float =>
          ret (DVALUE_Float (Float32.of_intu (repr (unsigned i1))))
        | DTYPE_I 8, DVALUE_Poison, DTYPE_Float =>
          ret DVALUE_Poison

        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Float =>
          ret (DVALUE_Float (Float32.of_intu (repr (unsigned i1))))
        | DTYPE_I 32, DVALUE_Poison, DTYPE_Float =>
          ret DVALUE_Poison

        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Float =>
          ret (DVALUE_Float (Float32.of_intu (repr (unsigned i1))))
        | DTYPE_I 64, DVALUE_Poison, DTYPE_Float =>
          ret DVALUE_Poison

        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Double =>
          ret (DVALUE_Double (Float.of_longu (repr (unsigned i1))))
        | DTYPE_I 1, DVALUE_Poison, DTYPE_Double =>
          ret DVALUE_Poison

        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Double =>
          ret (DVALUE_Double (Float.of_longu (repr (unsigned i1))))
        | DTYPE_I 8, DVALUE_Poison, DTYPE_Double =>
          ret DVALUE_Poison

        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Double =>
          ret (DVALUE_Double (Float.of_longu (repr (unsigned i1))))
        | DTYPE_I 32, DVALUE_Poison, DTYPE_Double =>
          ret DVALUE_Poison

        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Double =>
          ret (DVALUE_Double (Float.of_longu (repr (unsigned i1))))
        | DTYPE_I 64, DVALUE_Poison, DTYPE_Double =>
          ret DVALUE_Poison

        | _, _, _ => raise "ill typed Uitofp"
        end
      | Sitofp =>
        match t1, x, t2 with
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Float =>
          ret (DVALUE_Float (Float32.of_intu (repr (signed i1))))
        | DTYPE_I 1, DVALUE_Poison, DTYPE_Float =>
          ret DVALUE_Poison

        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Float =>
          ret (DVALUE_Float (Float32.of_intu (repr (signed i1))))
        | DTYPE_I 8, DVALUE_Poison, DTYPE_Float =>
          ret DVALUE_Poison

        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Float =>
          ret (DVALUE_Float (Float32.of_intu (repr (signed i1))))
        | DTYPE_I 32, DVALUE_Poison, DTYPE_Float =>
          ret DVALUE_Poison

        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Float =>
          ret (DVALUE_Float (Float32.of_intu (repr (signed i1))))
        | DTYPE_I 64, DVALUE_Poison, DTYPE_Float =>
          ret DVALUE_Poison

        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Double =>
          ret (DVALUE_Double (Float.of_longu (repr (signed i1))))
        | DTYPE_I 1, DVALUE_Poison, DTYPE_Double =>
          ret DVALUE_Poison

        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Double =>
          ret (DVALUE_Double (Float.of_longu (repr (signed i1))))
        | DTYPE_I 8, DVALUE_Poison, DTYPE_Double =>
          ret DVALUE_Poison

        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Double =>
          ret (DVALUE_Double (Float.of_longu (repr (signed i1))))
        | DTYPE_I 32, DVALUE_Poison, DTYPE_Double =>
          ret DVALUE_Poison

        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Double =>
          ret (DVALUE_Double (Float.of_longu (repr (signed i1))))
        | DTYPE_I 64, DVALUE_Poison, DTYPE_Double =>
          ret DVALUE_Poison

        | _, _, _ => raise "ill typed Sitofp"
        end
      | Fptoui
      | Fptosi
      | Fptrunc
      | Fpext => raise "TODO: unimplemented numeric conversion"
      | Inttoptr =>
        match t1, t2 with
        | DTYPE_I 64, DTYPE_Pointer => trigger (ItoP x)
        | _, _ => raise "ERROR: Inttoptr got illegal arguments"
        end
      | Ptrtoint =>
        match t1, t2 with
        | DTYPE_Pointer, DTYPE_I 64 => trigger (PtoI x)
        | _, _ => raise "ERROR: Ptrtoint got illegal arguments"
        end
      end.
    Arguments eval_conv_h _ _ _ _ : simpl nomatch.

    Definition eval_conv conv (t1:dtyp) x (t2:dtyp) : itree conv_E dvalue :=
      match t1, x with
      | DTYPE_I bits, dv =>
        eval_conv_h conv t1 dv t2
      | DTYPE_Vector s t, (DVALUE_Vector elts) =>
        (* In the future, implement bitcast and etc with vectors *)
        raise "vectors unimplemented"
      | _, _ => eval_conv_h conv t1 x t2
      end.
    Arguments eval_conv _ _ _ _ : simpl nomatch.

  End CONVERSIONS.

  Definition dv_zero_initializer (t:dtyp) : err dvalue :=
    failwith "dv_zero_initializer unimplemented".

  (* YZ: GlobalRead should always returns a dvalue. We can either carry the invariant, or cast [dvalue_to_uvalue] here *)
  Definition lookup_id (i:ident) : itree lookup_E uvalue :=
    match i with
    | ID_Global x => dv <- trigger (GlobalRead x);; ret (dvalue_to_uvalue dv)
    | ID_Local x  => trigger (LocalRead x)
    end.

(*
  [denote_exp] is the main entry point for evaluating itree expressions.
  top : is the type at which the expression should be evaluated (if any)
  INVARIANT:
    - top may be None only for
        - EXP_Ident
        - OP_* cases

    - top must be Some t for the remaining EXP_* cases
      Note that when top is Some t, the resulting dvalue can never be
      a function pointer for a well-typed itree program.

  Expressions are denoted as itrees that return a [dvalue].
 *)

  (* Instructions where division by 0 is UB *)
  Definition iop_is_div (iop : ibinop) : bool :=
    match iop with
    | UDiv _ => true
    | SDiv _ => true
    | URem   => true
    | SRem   => true
    | _      => false
    end.

  Definition fop_is_div (fop : fbinop) : bool :=
    match fop with
    | FDiv => true
    | FRem => true
    | _    => false
    end.

  Definition dvalue_not_zero (dv : dvalue) : Prop :=
    match dv with
    | DVALUE_I1 x     => x = zero
    | DVALUE_I8 x     => x = zero
    | DVALUE_I32 x    => x = zero
    | DVALUE_I64 x    => x = zero
    | DVALUE_Double x => x = Float.zero
    | DVALUE_Float x  => x = Float32.zero
    | _               => False
    end.

(*
  local: uvalue (fully blown)
  global: dvalue
  mem: dvalue + undef?
 *)

  (* YZ TODO: Need functor instance for undef_or_err *)

  Fixpoint denote_exp
           (top:option dtyp) (o:exp dtyp) {struct o} : itree exp_E uvalue :=
        let eval_texp '(dt,ex) := denote_exp (Some dt) ex
        in
        match o with
        | EXP_Ident i =>
          translate lookup_E_to_exp_E (lookup_id i)

        | EXP_Integer x =>
          match top with
          | None                => raise "denote_exp given untyped EXP_Integer"
          | Some (DTYPE_I bits) => lift_undef_or_err ret (fmap dvalue_to_uvalue (coerce_integer_to_int bits x))
          | _                   => raise "bad type for constant int"
          end

        | EXP_Float x =>
          match top with
          | None              => raise "denote_exp given untyped EXP_Float"
          | Some DTYPE_Float  => ret (UVALUE_Float (Float32.of_double x))
          | Some DTYPE_Double => ret (UVALUE_Double x)
          | _                 => raise "bad type for constant float"
          end

        | EXP_Hex x =>
          match top with
          | None              => raise "denote_exp given untyped EXP_Hex"
          | Some DTYPE_Float  => ret (UVALUE_Float (Float32.of_double x))
          | Some DTYPE_Double => ret (UVALUE_Double x)
          | _                 => raise "bad type for constant hex float"
          end

        | EXP_Bool b =>
          match b with
          | true  => ret (UVALUE_I1 one)
          | false => ret (UVALUE_I1 zero)
          end

        | EXP_Null => ret (UVALUE_Addr A.null)

        | EXP_Zero_initializer =>
          match top with
          | None   => raise "denote_exp given untyped EXP_Zero_initializer"
          | Some t => lift_err ret (fmap dvalue_to_uvalue (dv_zero_initializer t))
          end

        | EXP_Cstring s => raise "EXP_Cstring not yet implemented"

        | EXP_Undef =>
          match top with
          | None   => raise "denote_exp given untyped EXP_Undef"
          | Some t => ret (UVALUE_Undef t)
          end

        (* Question: should we do any typechecking for aggregate types here? *)
        (* Option 1: do no typechecking: *)
        | EXP_Struct es =>
          vs <- map_monad eval_texp es ;;
          ret (UVALUE_Struct vs)

        (* Option 2: do a little bit of typechecking *)
        | EXP_Packed_struct es =>
          match top with
          | None => raise "denote_exp given untyped EXP_Struct"
          | Some (DTYPE_Packed_struct _) =>
            vs <- map_monad eval_texp es ;;
            ret (UVALUE_Packed_struct vs)
          | _ => raise "bad type for VALUE_Packed_struct"
          end

        | EXP_Array es =>
          vs <- map_monad eval_texp es ;;
          ret (UVALUE_Array vs)

        | EXP_Vector es =>
          vs <- map_monad eval_texp es ;;
          ret (UVALUE_Vector vs)

        | OP_IBinop iop dt op1 op2 =>
          v1 <- denote_exp (Some dt) op1 ;;
          v2 <- denote_exp (Some dt) op2 ;;
          if iop_is_div iop && negb (is_concrete v2)
          then
            dv2 <- trigger (pick v2 (forall dv2, concretize v2 dv2 -> dvalue_not_zero dv2)) ;;
            uvalue_to_dvalue_binop2
              (fun v1 v2 => ret (UVALUE_IBinop iop v1 v2))
              (fun v1 v2 => translate _failure_UB_to_ExpE
                                   (lift_undef_or_err ret (fmap dvalue_to_uvalue (eval_iop iop v1 v2))))
              v1 dv2
          else
            uvalue_to_dvalue_binop
              (fun v1 v2 => ret (UVALUE_IBinop iop v1 v2))
              (fun v1 v2 => translate _failure_UB_to_ExpE
                                   (lift_undef_or_err ret (fmap dvalue_to_uvalue (eval_iop iop v1 v2))))
              v1 v2

        | OP_ICmp cmp dt op1 op2 =>
          v1 <- denote_exp (Some dt) op1 ;;
          v2 <- denote_exp (Some dt) op2 ;;
          uvalue_to_dvalue_binop
            (fun v1 v2 => ret (UVALUE_ICmp cmp v1 v2))
            (fun v1 v2 => lift_undef_or_err ret (fmap dvalue_to_uvalue (eval_icmp cmp v1 v2)))
            v1 v2

        | OP_FBinop fop fm dt op1 op2 =>
          v1 <- denote_exp (Some dt) op1 ;;
          v2 <- denote_exp (Some dt) op2 ;;
          if fop_is_div fop && negb (is_concrete v2)
          then
            dv2 <- trigger (pick v2 (forall dv2, concretize v2 dv2 -> dvalue_not_zero dv2)) ;;
            uvalue_to_dvalue_binop2
              (fun v1 v2 => ret (UVALUE_FBinop fop fm v1 v2))
              (fun v1 v2 => translate _failure_UB_to_ExpE
                                   (lift_undef_or_err ret (fmap dvalue_to_uvalue (eval_fop fop v1 v2))))
              v1 dv2
          else
            uvalue_to_dvalue_binop
              (fun v1 v2 => ret (UVALUE_FBinop fop fm v1 v2))
              (fun v1 v2 => translate _failure_UB_to_ExpE
                                   (lift_undef_or_err ret (fmap dvalue_to_uvalue (eval_fop fop v1 v2))))
              v1 v2

        | OP_FCmp fcmp dt op1 op2 =>
          v1 <- denote_exp (Some dt) op1 ;;
          v2 <- denote_exp (Some dt) op2 ;;
          uvalue_to_dvalue_binop
            (fun v1 v2 => ret (UVALUE_FCmp fcmp v1 v2))
            (fun v1 v2 => lift_undef_or_err ret (fmap dvalue_to_uvalue (eval_fcmp fcmp v1 v2)))
            v1 v2

        | OP_Conversion conv dt1 op t2 =>
          v <- denote_exp (Some dt1) op ;;
          uvalue_to_dvalue_uop
            (fun v => ret (UVALUE_Conversion conv v t2))
            (fun v => translate conv_E_to_exp_E
                             (fmap dvalue_to_uvalue (eval_conv conv dt1 v t2)))
            v

        (* CB TODO: Do we actually need to pick here? GEP doesn't do any derefs. Does it make sense to leave it as a UVALUE? *)
        | OP_GetElementPtr dt1 (dt2, ptrval) idxs =>
          vptr <- denote_exp (Some dt2) ptrval ;;
          vs <- map_monad (fun '(_, index) => denote_exp (Some (DTYPE_I 32)) index) idxs ;;

          let maybe_dvs := dvptr <- uvalue_to_dvalue vptr ;;
                           dvs <- map_monad uvalue_to_dvalue vs ;;
                           ret (dvptr, dvs)
          in

          match maybe_dvs with
          | inr (dvptr, dvs) => fmap dvalue_to_uvalue (trigger (GEP dt1 dvptr dvs))
          | inl _ =>
            (* Pick to get dvalues *)
            dvptr <- trigger (pick vptr True) ;;
            dvs <- map_monad (fun v => trigger (pick v True)) vs ;;

            fmap dvalue_to_uvalue (trigger (GEP dt1 dvptr dvs))
          end

        | OP_ExtractElement vecop idx =>
          (*  'vec <- monad_app_snd (denote_exp e) vecop;
              'vidx <- monad_app_snd (denote_exp e) idx;  *)
          raise "extractelement not implemented" (* TODO: Extract Element *)

        | OP_InsertElement vecop eltop idx =>
          (*  'vec <- monad_app_snd (denote_exp e) vecop;
              'v <- monad_app_snd (denote_exp e) eltop;
              'vidx <- monad_app_snd (denote_exp e) idx; *)
          raise "insertelement not implemented" (* TODO *)

        | OP_ShuffleVector vecop1 vecop2 idxmask =>
          (*  'vec1 <- monad_app_snd (denote_exp e) vecop1;
              'vec2 <- monad_app_snd (denote_exp e) vecop2;
              'vidx <- monad_app_snd (denote_exp e) idxmask; *)
          raise "shufflevector not implemented" (* TODO *)

        | OP_ExtractValue (dt, str) idxs =>
          str <- denote_exp (Some dt) str;;
          let fix loop str idxs : undef_or_err uvalue :=
              match idxs with
              | [] => ret str
              | i :: tl =>
                v <- index_into_str str i ;;
               loop v tl
              end in
          lift_undef_or_err ret (loop str idxs)

        | OP_InsertValue strop eltop idxs =>
          (*
            '(t1, str) <- monad_app_snd (denote_exp e) strop;
            '(t2, v) <- monad_app_snd (denote_exp e) eltop;
            let fix loop str idxs : err dvalue :=
            match idxs with
            | [] => raise "invalid indices"
            | [i] =>
            insert_into_str str v i
            | i :: tl =>
            '(_, v) <- index_into_str str i;
            'v <- loop v tl;
            insert_into_str str v i
            end in
            loop str idxs*)
          raise "TODO"

        | OP_Select (dt, cnd) (dt1, op1) (dt2, op2) =>
          cndv <- denote_exp (Some dt) cnd ;;
          v1   <- denote_exp (Some dt1) op1 ;;
          v2   <- denote_exp (Some dt2) op2 ;;
          match uvalue_to_dvalue cndv with
          | inl e => ret (UVALUE_Select cndv v1 v2)
          | inr dcndv => lift_undef_or_err ret (eval_select dcndv v1 v2)
          end
        end.
      Arguments denote_exp _ : simpl nomatch.

      Definition eval_op (o:exp dtyp) : itree exp_E uvalue :=
        denote_exp None o.
      Arguments eval_op _ : simpl nomatch.

      (* An instruction has only side-effects, it therefore returns [unit] *)

      Definition denote_instr
                 (i: (instr_id * instr dtyp)): itree instr_E unit :=
        match i with
        (* Pure operations *)

        | (IId id, INSTR_Op op) =>
          dv <- translate exp_E_to_instr_E (eval_op op) ;;
          trigger (LocalWrite id dv)

        (* Allocation *)
        | (IId id, INSTR_Alloca dt _ _) =>
          dv <- trigger (Alloca dt);;
          trigger (LocalWrite id (dvalue_to_uvalue dv))

        (* Load *)
        | (IId id, INSTR_Load _ dt (du,ptr) _) =>
          ua <- translate exp_E_to_instr_E (denote_exp (Some du) ptr) ;;
          da <- trigger (pick ua True) ;;
          match da with
          | DVALUE_Poison => raiseUB "Load from poisoned address."
          | _ => dv <- trigger (Load dt da);;
                trigger (LocalWrite id dv)
          end

        (* Store *)
        | (IVoid _, INSTR_Store _ (dt, val) (du, ptr) _) =>
          uv <- translate exp_E_to_instr_E (denote_exp (Some dt) val) ;;
          dv <- trigger (pick uv True) ;;
          ua <- translate exp_E_to_instr_E (denote_exp (Some du) ptr) ;;
          da <- trigger (pick ua (exists x, forall da, concretize ua da -> da = x)) ;;
          match da with
          | DVALUE_Poison => raiseUB "Store to poisoned address."
          | _ => trigger (Store da dv)
          end

        | (_, INSTR_Store _ _ _ _) => raise "ILL-FORMED itree ERROR: Store to non-void ID"

        (* Call *)
        (* CB TODO: Do we need to pick here? *)
        | (pt, INSTR_Call (dt, f) args) =>
          debug ("call") ;;
          uvs <- map_monad (fun '(t, op) => (translate exp_E_to_instr_E (denote_exp (Some dt) op))) args ;;
          dvs <- map_monad (fun x => trigger (pick x True)) uvs ;;
          returned_value <- 
          match Intrinsics.intrinsic_exp f with
          | Some s =>
            dv <- trigger (Intrinsic dt s dvs) ;;
            ret (dvalue_to_uvalue dv)
          | None =>
            fv <- translate exp_E_to_instr_E (denote_exp None f) ;;
            dfv <- trigger (pick fv True) ;; (* TODO, should this be unique? *)
            trigger (Call dt dfv dvs)
          end
          ;;
          match pt with
          | IVoid _ => ret tt
          | IId id  => trigger (LocalWrite id returned_value)
          end

        | (_, INSTR_Comment _) => ret tt

        | (_, INSTR_Unreachable) => raise "IMPOSSIBLE: unreachable in reachable position"

        (* Currently unhandled itree instructions *)
        | (_, INSTR_Fence)
        | (_, INSTR_AtomicCmpXchg)
        | (_, INSTR_AtomicRMW)
        | (_, INSTR_VAArg)
        | (_, INSTR_LandingPad) => raise "Unsupported itree instruction"

        (* Error states *)
        | (_, _) => raise "ID / Instr mismatch void/non-void"

        end.

      (* A [terminator] either returns from a function call, producing a [dvalue],
         or jumps to a new [block_id]. *)
      Definition denote_terminator (t: terminator dtyp): itree exp_E (block_id + uvalue) :=
        match t with

        | TERM_Ret (dt, op) =>
          dv <- denote_exp (Some dt) op ;;
             (* YZ : Hesitant between three options.
                1. emit the pop events here and return the dvalue (current choice);
                2. introduce a Return event that would be handled at the same time as Call and do it;
                3. mix of both: can return the dynamic value and have no Ret event, but pop in denote_mcfg
              *)
          (* trigger LocalPop;;  *) (* TODO: actually done in denote_mcfg. Remove after validation *)
          ret (inr dv)

        | TERM_Ret_void =>
          (* trigger LocalPop;;  *) (* TODO: actually done in denote_mcfg. Remove after validation *)
          ret (inr UVALUE_None)

        | TERM_Br (dt,op) br1 br2 =>
          uv <- denote_exp (Some dt) op ;;
          match uv with
          | UVALUE_I1 comparison_bit =>
            if eq comparison_bit one then
              ret (inl br1)
            else
              ret (inl br2)
          | UVALUE_Poison => raiseUB "Branching on poison."
          | _ => raise "Br got non-bool value"
          end

        | TERM_Br_1 br => ret (inl br)

        (* Currently unhandled itree terminators *)
        | TERM_Switch _ _ _
        | TERM_IndirectBr _ _
        | TERM_Resume _
        | TERM_Invoke _ _ _ _ => raise "Unsupport itree terminator"
        end.

      (* Denoting a list of instruction simply binds the trees together *)
      Fixpoint denote_code (c: code dtyp): itree instr_E unit :=
        match c with
        | nil => ret tt
        | i::c => denote_instr i;; denote_code c
        end.

      (* A block ends with a terminator, it either jumps to another block,
         or returns a dynamic value *)
      Definition denote_block (b: block dtyp) : itree instr_E (block_id + uvalue) :=
        denote_code (blk_code dtyp b);;
        translate exp_E_to_instr_E (denote_terminator (snd (blk_term dtyp b))).

      (* YZ FIX: no need to push/pop, but do all the assignments afterward *)
      (* One needs to be careful when denoting phi-nodes: they all must
         be evaluated in the same environment.
         We therefore starts the denotation of a phi-node by pushing a
         local copy of the environment of the stack, that we pop back
         once we are finished evaluating the expression.
         We then bind the resulting value in the underlying environment.
       *)

      Definition denote_phi (bid : block_id) (id_p : local_id * phi dtyp) : itree exp_E (local_id * uvalue) :=
        let '(id, Phi dt args) := id_p in
        match assoc RawIDOrd.eq_dec bid args with
        | Some op =>
          uv <- denote_exp (Some dt) op ;;
          ret (id,uv)
        | None => raise ("jump: phi node doesn't include block " ++ to_string bid)
        end.

      (* Our denotation currently contains two kinds of indirections: jumps to labels, internal to
         a cfg, and calls to functions, that jump from a cfg to another.
         In order to denote a single [cfg], we tie the first knot by linking together all the blocks
         contain in the [cfg].
         Note that contrary to calls, no events have been explicitely introduced for internal jumps.
         This is due to the _tail recursive_ nature of these jumps: they only occur as the last
         instruction of blocks. We hence can use a [loop] operator to do the linking, as opposed
         to the more general [mrec] operator that will be used to link internal calls.
       *)
      (* The idea here is simply to enter the body through the [init] [block_id] of the [cfg].
         As long as the computation returns a new label to jump to, we feed it back to the loop.
         If it ever returns a dynamic value, we exit the loop by returning the [dvalue].
       *)
      (* Note that perhaps surprisingly, this is the place where phi-nodes get handled.
         The intuition is that the semantics of phi-nodes depends on the identity of the block
         jumping into the phi-nodes. It's hence actually at the time the jump is performed that
         we have enough information to perform it.
       *)
      (* YZ Note: This should be sufficient to denote itree programs.
         However, it does not give a denotation to open fragments of a [cfg], which might be
         useful to facilitate some reasoning.
         To do so, we would need to introduce sub-types of the universe of [block_id] and expose
         in the type of the constructions the interface of the components, in a fashion similar
         to the _Asm_ language introduced in the ICFP paper on itrees.
       *)
      (*
        We actually might be able to denote open programs without sending things at the level
        of types, just by deciding internally to loop or not and not reflect the invariant
        in the type.
       *)
      Definition denote_cfg (f: cfg dtyp) : itree instr_E uvalue :=
        loop (fun (bid : block_id + block_id) =>
                match bid with
                | inl bid
                | inr bid =>
                  match find_block dtyp (blks _ f) bid with
                  | None => raise ("Can't find block in denote_cfg " ++ to_string bid)
                  | Some block =>
                    (* We denote the block *)
                    bd <- denote_block block;;
                    (* And set the phi-nodes of the new destination, if any *)
                    match bd with
                    | inr dv => ret (inr dv)
                    | inl bid =>
                      debug ("phi") ;;
                      dvs <- map_monad
                          (fun x => translate exp_E_to_instr_E (denote_phi bid x))
                          (blk_phis _ block) ;;
                      map_monad (fun '(id,dv) => trigger (LocalWrite id dv)) dvs;;
                      ret (inl bid)
                    end
                  end
                end
             ) (init _ f).

      (* TODO : Move this somewhere else *)
      Fixpoint combine_lists_err {A B:Type} (l1:list A) (l2:list B) : err (list (A * B)) :=
        match l1, l2 with
        | [], [] => ret []
        | x::xs, y::ys =>
          l <- combine_lists_err xs ys ;;
            ret ((x,y)::l)
        | _, _ => failwith "combine_lists_err: different length lists"
        end.


      (* The denotation of an itree function is a coq function that takes
         a list of dvalues and returns the appropriate semantics. *)
      Definition function_denotation : Type :=
          list dvalue -> itree fun_E uvalue.

      Definition denote_function (df:definition dtyp (cfg dtyp)) : function_denotation  :=
        fun (args : list dvalue) =>
          (* We match the arguments variables to the inputs *)
          bs <- lift_err ret (combine_lists_err (df_args dtyp _ df) args) ;;
             (* generate the corresponding writes to the local stack frame *)
          trigger MemPush ;;
          trigger (StackPush (map (fun '(k,v) => (k, dvalue_to_uvalue v)) bs)) ;;
          rv <- translate instr_E_to_fun_E (denote_cfg (df_instrs dtyp _ df)) ;;
          trigger StackPop ;;
          trigger MemPop ;;
          ret rv.

      (* We now turn to the second knot to be tied: a top-level itree program is a set
         of mutually recursively defined functions, i.e. [cfg]s. We hence need to
         resolve this mutually recursive definition by interpreting away the call events.
         As mentionned above, calls are not tail recursive: we need a more general fixpoint
         operator than [loop], which [mrec] provides.
       *)
      (* A slight complication comes from the fact that not all call events will be interpreted
         away as such. Some of them correspond to external calls -- or to intrinsics -- that will
         be kept uninterpreted for now.
         Since the type of [mrec] forces us to get rid of the [CallE] family of events that we
         interpret, we therefore cast external calls into an isomorphic family of events
         that life in the "right" injection of the [_CFG_INTERNAL] effect
       *)

(* SAZ: for "open" MCFGs we have
    - (m_declarations CFG) is the set of possible ExternalCalls
    - (List.map df_prototype (m_definitions CFG)) is the set of possilbe Entry Functions  (also internal calls)
 *)
      Definition lookup_defn {B} := (@assoc _ B (@dvalue_eq_dec)).



      (* YZ Note: we could have chosen to distinguish both kinds of calls in [denote_instr] *)
      Definition denote_mcfg
                 (fundefs:list (dvalue * function_denotation)) (dt : dtyp)
                 (f_value : dvalue) (args : list dvalue) : itree _ uvalue :=
          @mrec CallE (CallE +' _)
                (fun T call =>
                   match call with
                   | Call dt fv args =>
                     match (lookup_defn fv fundefs) with
                     | Some f_den => (* If the call is internal *)
                       (* and denote the [cfg]. *)
                       translate _funE_to_INTERNAL (f_den args)
                     | None =>
                       (* This must have been a registered external function  *)
                       (* We _don't_ push a itree stack frame, since the external *)
                       (* call takes place in one "atomic" step.
                          SAZ: Not sure that we shouldn't at least push the memory frame
                        *)

                       (* We cast the call into an external CallE *)
                       trigger (ExternalCall dt fv args)
                     end
                   end
                ) _ (Call dt f_value args).
End Denotation.

  (****************************** SCRAPYARD ******************************)

  (* Code related to environment unused for global env that are static.
     Should be reused to handle locals.
   *)
(*
Definition env  := ENV.t dvalue.

Definition env_of_assoc {A} (l:list (raw_id * A)) : ENV.t A :=
  List.fold_left (fun e '(k,v) => ENV.add k v e) l (@ENV.empty A).


  Fixpoint string_of_env' (e:list (raw_id * dvalue)) :=
    match e with
    | [] => empty
    | (lid, _)::rest => ((to_string lid) << " " << (string_of_env' rest))%show
    end.

  Instance show_env : Show env := fun env => string_of_env' (ENV.elements env).
  Definition add_env := ENV.add.
*)
  (* Code related to the previous structure of states.
     Will likely not be reused as is. The structure of states should now be
     defined by successive states monads introduced by sucessive handlers.
   *)
(*
  Inductive frame : Type :=
  | KRet      (e:env) (id:local_id) (q:pc)
  | KRet_void (e:env) (p:pc)
  .
  Definition stack := list frame.

  Definition state := (genv * pc * env * stack)%type.

  Definition pc_of (s:state) :=
    let '(g, p, e, k) := s in p.

  Definition env_of (s:state) :=
    let '(g, p, e, k) := s in e.

  Definition stack_of (s:state) :=
    let '(g, p, e, k) := s in k.
*)

  (* Code related to manipulating the stack frame during a return *)
  (* Should be mostly irrelevant, but needs to be pondered. *)
  (* The local env aspect should be handled by interpreting Locals into
   a stack of environment. The ret terminator introduces a special pop
   event when denoted.
   The id part, hosting the returned value, should be handled by being given
   to the denotation of the Call instruction: it is a call event, expected a
   dvalue, followed by the appropriate store event.
   The program counter part should be irrelevant in this style of semantics.
   *)

    (* match k with *)
    (* | [] => halt dv        *)
    (* | (KRet e' id p') :: k' => cont (g, p', add_env id dv e', k') *)
    (* | _ => raise_p pc "IMPOSSIBLE: Ret op in non-return configuration"  *)
    (* end *)

  (* match k with *)
    (* | [] => halt DVALUE_None *)
    (* | (KRet_void e' p')::k' => cont (g, p', e', k') *)
    (* | _ => raise_p pc "IMPOSSIBLE: Ret void in non-return configuration" *)
    (* end *)


(* Defining the Global Environment ------------------------------------------------------- *)
(*

*)
(* Assumes that the entry-point function is named "fname" and that it takes
   no parameters *)

(* COMMENTING OUT
Definition init_state (fname:string) : itree (failureE +' debugE) state :=
  g <- build_global_environment ;;
  fentry <- trywith ("INIT: no function named " ++ fname) (find_function_entry CFG (Name fname)) ;;
  let 'FunctionEntry ids pc_f := fentry in
    ret (g, pc_f, (@ENV.empty dvalue), []).

CoFixpoint step_sem (r:result) : itree (failureE +' debugE) dvalue :=
  match r with
  | Done v => ret v
  | Step s => x <- step s ;; ITreeDefinition.Tau (step_sem x)
  end.

(* TODO: move elsewhere? *)
Fixpoint combine_lists_err {A B:Type} (l1:list A) (l2:list B) : err (list (A * B)) :=
  match l1, l2 with
  | [], [] => ret []
  | x::xs, y::ys =>
    l <- combine_lists_err xs ys ;;
    ret ((x,y)::l)
  | _, _ => failwith "combine_lists_err: different lenth lists"
  end.

END OF COMMENTING OUT *)
(*
YZ : Should not be used anymore?
Inductive result :=
| Done (v:dvalue)
| Step (s:state)
.

Definition raise_p {X} (p:pc) s : itree (failureE +' debugE) X := raise (s ++ " in block: " ++ (to_string p)).
Definition cont (s:state)  : itree (failureE +' debugE) result := ret (Step s).
Definition halt (v:dvalue) : itree (failureE +' debugE) result := ret (Done v).

 *)
(*
Definition jump (fid:function_id) (bid_src:block_id) (bid_tgt:block_id) (g:genv) (e_init:env) (k:stack) : itree (failureE +' debugE) result :=
  let eval_phi (e:env) '(iid, Phi t ls) :=
      match assoc RawIDOrd.eq_dec bid_src ls with
      | Some op =>
        let dt := eval_typ t in
        dv <- denote_exp g (Some dt) op ;;
        ret (add_env iid dv e)
      | None => raise ("jump: phi node doesn't include block " ++ to_string bid_src )
      end
  in
  debug ("jumping to: " ++ to_string bid_tgt) ;;
  match find_block_entry CFG fid bid_tgt with
  | None => raise ("jump: target block " ++ to_string bid_tgt ++ " not found")
  | Some (BlockEntry phis pc_entry) =>
      e_out <- monad_fold_right eval_phi phis e_init ;;
      cont (g, pc_entry, e_out, k)
  end.
 *)

    (* YZ: where will this pc_next be relevant now? Likely when looping I think. *)
    (* do pc_next <- trywith "no fallthrough instruction" (incr_pc CFG pc) ;; *)
    (* match (pt pc), insn  with *)

(* YZ : How should we do handle phi nodes?
       Seems like option 4 is the way to go.
       OPTION 1:
       [| block|]: (block_id * block_id) -> itreeE (block_id * block_id)
       i.e. We treat elementary blocks as having several entry point, one per
       adress from which we jumped into it.
       OPTION 2:
       We actually perform the semantics of phi nodes at the end of the denotation
       of the jumping block.
       i.e. : if b1 := jmp b2 and b2 := x = phi (b1,1; b3,3)
       then [b1] = send (LocalWrite x 1);; ret b2
       and of course we do not denote phi nodes first when denoting blocks.
       Issue (?) Doesn't it break modularity? Can we still loop to tie those things
       together?
       OPTION 3:
       Could the semantics of the phi node use a special event asking the environment
       where it comes from, and the semantics of the ret using a special event telling
       the world it's jumping?
       That kinda implies that now we have two level of handling the control flow of a
       single function, but avoids both ugly pairs and is completely modular.
       OPTION 4:
       Actually, it might be in the function provided to [loop] when denoting
       a collection of blocks that this should take place so that there is no
       need for a new effect, it's just that the jmp one does more work.
     *)
(*
      match (find_function_entry CFG fid) with
      | Some fnentry =>
        let 'FunctionEntry ids pc_f := fnentry in
        bs <- combine_lists_err ids dvs ;;
        let env := env_of_assoc bs in
        match pt with
        | IVoid _ =>
          (debug "pushed void stack frame") ;;
          cont (g, pc_f, env, (KRet_void e pc_next::k))
        | IId id =>
          (debug "pushed non-void stack frame") ;;
          cont (g, pc_f, env, (KRet e id pc_next::k))
        end
      | None =>
        (* This must have been a registered external function  *)
        (* We _don't_ push a itree stack frame, since the external *)
        (* call takes place in one "atomic" step. *)

        match fid with
        | Name s =>
          match pt with
          | IVoid _ =>  (* void externals don't return a value *)
            vis (Call (eval_typ t) s dvs) (fun dv => cont (g, pc_next, e, k))

                   | IId id => (* non-void externals are assumed to be type correct and bind a value *)
                     vis (Call (eval_typ t) s dvs)
                         (fun dv => cont (g, pc_next, add_env id dv e, k))
                   end
                 | _ => raise ("step: no function " (* ++ (string_of fid) *))
                 end
      end
       *)
