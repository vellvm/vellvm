(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)
(* begin hide *)

From Coq Require Import
     ZArith String List
     FSets.FMapWeakList
     Bool.Bool.

Require Import Integers Floats.

From ExtLib Require Import
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
     Handlers.Intrinsics.

Require Import Ceres.Ceres.

(* YZ: Undesirable dependency on Handlers/Intrinsics: move [intrinsic_exp] somewhere else? *)

Import Sum.
Import Subevent.
Import EqvNotation.
Import ListNotations.
Import MonadNotation.

Set Implicit Arguments.
Set Contextual Implicit.

Open Scope monad_scope.
Open Scope string_scope.
Open Scope Z_scope.

(* end hide *)

(** ** Uninterpreted denotation
    In this file, we define the first layer of denotation of _VIR_.

    More specifically, we follow the overall structure of itree-based denotations which consist
    in splitting the process in two main phases:
    1. Denote syntactic entities in terms of uninterpreted itrees, where syntactic events are carried in the tree.
    2. Interpret these itrees into the appropriate monad to implement the effect of these events.

    This file implements step 1: to a [mcfg], and to every internal syntactic constructs of _VIR_, we associate
    an uninterpreted interaction tree.

    The interface of events used for this denotation is defined in LLVMEvents.v. Roughly speaking, they include:
     - Internal Calls                                 (CallE)
     - External Calls                                 (ExtrernalCallE)
     - Calls to Intrinsics                            (IntrinsicE and MemoryIntrinsicE)
     - Manipulation of the global environment         (LLVMGEnvE)
     - Manipulation of the local environment          (LLVMEnvE)
     - Manipulation of the stack of local environment (LLVMStackE)
     - Manipulation of the memory                     (MemoryE)
     - Determination of undef                         (PickE)
     - Undefined behavior                             (UBE)
     - Failure                                        (FailureE)
     - Debugging                                      (DebugE)


    The exact interface used by each denotation function depends slightly on the object of consideration.
    Most specifically, three interfaces are used.
    - At the top level, in order to denote whole _VIR_ programs, we use the interface:
      L0 ::=  ExternalCallE +' IntrinsicE +' LLVMGEnvE +' (LLVMEnvE +' LLVMStackE) +' MemoryE +' PickE +' UBE +' DebugE +' FailureE. 
      Noticeable:
      * there are no more internal calls, they are resolved through the itree combinator
        for mutual recursiion [mrec].
    - For individual [cfg] (i.e. VIR functions) and most of their internal components:
      [instr_E ::= CallE +' IntrinsicE +' LLVMGEnvE +' LLVMEnvE +' MemoryE +' PickE +' UBE +' DebugE +' FailureE].
      Noticeable:
      * there are no external calls: the distinction between internal and external is only made once we
        tie the mutually recursive knot.
      * there are no manipulation of the stack: internally to a function, the denotation only sees the
        current local stack. The stack discipline is handled when tying the knot.
    - For expressions [exp], we specialize further the interface:
      [exp_E ::= LLVMGEnvE +' LLVMEnvE +' MemoryE +' PickE +' UBE +' DebugE +' FailureE].
      The rationale for this restriction is that we need to denote expressions both internally to cfgs
      of course, but also at the [mcfg] level to perform the initialization of the memory.
      We therefore need to be able to inject their signature into both [L0] and [instr_E].

    The effect of each event used through this first phase is defined by the corresponding [handler] in
    the Handlers repository. These handlers are chained together to form the interpretation of the
    itrees in the second phase.
 *)

(* YZ Ask Steve: why is LLVMEvents an argument to the functor rather than have Make(A) inside the module? *)
Module Denotation(A:MemoryAddress.ADDRESS)(LLVMEvents:LLVM_INTERACTIONS(A)).
  Import LLVMEvents.

  Section CONVERSIONS.

    (** ** Typed conversion
        Performs a dynamic conversion of a [dvalue] of type [t1] to one of type [t2].
        For instance, convert an integer over 8 bits to one over 1 bit by truncation.

        The conversion function is not pure, i.e. in particular cannot live in [DynamicValues.v]
        as would be natural, due to the [Int2Ptr] and [Ptr2Int] cases. At those types, the conversion
        needs to cast between integers and pointers, which depends on the memory model.
     *)

    (* Note: Inferring the subevent instance takes a small but non-trivial amount of time,
       and has to be done here hundreds and hundreds of times due to the brutal pattern matching on
       several values. Factoring the inference upfront is therefore necessary.
     *)
    (* YZ: Loosen [conv_E] into [exp_E] to reduce the number of interfaces at play? *)
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
        | DTYPE_Pointer, DTYPE_I _ => trigger (PtoI t2 x)
        | _, _ => raise "ERROR: Ptrtoint got illegal arguments"
        end
      end.
    Arguments eval_conv_h _ _ _ _ : simpl nomatch.

    Definition eval_conv (conv : conversion_type) (t1 : dtyp) (x : dvalue) (t2:dtyp) : itree conv_E dvalue :=
      match t1, x with
      | DTYPE_Vector s t, (DVALUE_Vector elts) =>
        (* In the future, implement bitcast and etc with vectors *)
        raise "vectors unimplemented"
      | _, _ => eval_conv_h conv t1 x t2
      end.
    Arguments eval_conv _ _ _ _ : simpl nomatch.

  End CONVERSIONS.

  Definition dv_zero_initializer (t:dtyp) : err dvalue :=
    failwith "dv_zero_initializer unimplemented".

  (** ** Ident lookups
      Look-ups depend on the nature of the [ident], that may be local or global.
      In each case, we simply trigger the corresponding read event.
      Note: global maps contain [dvalue]s, while local maps contain [uvalue]s.
      We perform the conversion here.
   *)
  (* YZ: Loosen [lookup_E] into [exp_E] to reduce the number of interfaces at play? *)
  Definition lookup_id (i:ident) : itree lookup_E uvalue :=
    match i with
    | ID_Global x => dv <- trigger (GlobalRead x);; ret (dvalue_to_uvalue dv)
    | ID_Local x  => trigger (LocalRead x)
    end.

  (* YZ TODO: move these somewhere else (DynamicValues most likely) *)

  (* Instructions for which division by 0 is an undefined behavior *)
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

  (* Predicate testing whether a [dvalue] is equal to zero at its type *)
  Definition dvalue_is_zero (dv : dvalue) : Prop :=
    match dv with
    | DVALUE_I1 x     => x = zero
    | DVALUE_I8 x     => x = zero
    | DVALUE_I32 x    => x = zero
    | DVALUE_I64 x    => x = zero
    | DVALUE_Double x => x = Float.zero
    | DVALUE_Float x  => x = Float32.zero
    | _               => False
    end.

  Definition dvalue_not_zero dv := ~ (dvalue_is_zero dv).

  (* A trivially concrete [uvalue] does not need to go through a pick event to get concretize.
     This function therefore either trigger [pick], or perform a direct cast.
     The value of this "optimization" is debatable. *)
  Definition concretize_or_pick {E : Type -> Type} `{PickE -< E} `{FailureE -< E} (uv : uvalue) (P : Prop) : itree E dvalue :=
    if is_concrete uv
    then lift_err ret (uvalue_to_dvalue uv)
    else trigger (pick uv P).
  
  (* Pick a possibly poison value, treating poison as nondeterminism.
     This is used for freeze. *)
  Definition pick_your_poison {E : Type -> Type} `{PickE -< E} `{FailureE -< E} (dt : dtyp) (uv : uvalue) : itree E dvalue :=
    match uv with
    | UVALUE_Poison => concretize_or_pick (UVALUE_Undef dt) True
    | _             => concretize_or_pick uv True
    end.

  Definition pickUnique {E : Type -> Type} `{PickE -< E} `{FailureE -< E} (uv : uvalue) : itree E dvalue
    := concretize_or_pick uv (unique_prop uv).

  (** ** Denotation of expressions
      [denote_exp top o] is the main entry point for evaluating itree expressions.
      top : the type at which the expression should be evaluated (if any)
      o   : the expression to be evaluated
      INVARIANT:
       - top may be None only for
        + EXP_Ident
        + OP_* cases

     Note that when top is Some t, the resulting dvalue can never be a function pointer
     for a well-typed itree program.

     Expressions are denoted as itrees that return a [uvalue].
 *)

  Fixpoint denote_exp
           (top:option dtyp) (o:exp dtyp) {struct o} : itree exp_E uvalue :=
        let eval_texp '(dt,ex) := denote_exp (Some dt) ex
        in
        match o with

        (* The translation injects the [lookup_E] interface used by [lookup_id] to the ambient one *)
        | EXP_Ident i =>
          translate lookup_E_to_exp_E (lookup_id i)

        | EXP_Integer x =>
          match top with
          | None                => raise "denote_exp given untyped EXP_Integer"
          | Some (DTYPE_I bits) => lift_undef_or_err ret (fmap dvalue_to_uvalue (coerce_integer_to_int bits x))
          | Some typ            => raise ("bad type for constant int: " ++ to_string typ)
          end

        | EXP_Float x =>
          match top with
          | None              => raise "denote_exp given untyped EXP_Float"
          | Some DTYPE_Float  => ret (UVALUE_Float x)
          | _                 => raise "bad type for constant float"
          end

        | EXP_Double x =>
          match top with
          | None              => raise "denote_exp given untyped EXP_Double"
          | Some DTYPE_Double => ret (UVALUE_Double x)
          | _                 => raise "bad type for constant double"
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

        (* YZ TODO : Unsure what this means. Expand on it *)
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

        (* The semantics of operators is complicated by both uvalues and
           undefined behaviors.
           We denote each operands first, but the denotation of the operator itself
           depends on whether it may raise UB, and how.
         *)
        | OP_IBinop iop dt op1 op2 =>
          v1 <- denote_exp (Some dt) op1 ;;
          v2 <- denote_exp (Some dt) op2 ;;
          if iop_is_div iop && negb (is_concrete v2)
          then
            dv2 <- concretize_or_pick v2 (forall dv2, concretize v2 dv2 -> dvalue_not_zero dv2) ;;
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
            dv2 <- concretize_or_pick v2 (forall dv2, concretize v2 dv2 -> dvalue_is_zero dv2) ;;
            uvalue_to_dvalue_binop2
              (fun v1 v2 => ret (UVALUE_FBinop fop fm v1 v2))
              (fun v1 v2 =>
                 translate _failure_UB_to_ExpE
                                   (lift_undef_or_err ret (fmap dvalue_to_uvalue (eval_fop fop v1 v2))))
              v1 dv2
          else
            uvalue_to_dvalue_binop
            (fun v1 v2 =>
               ret (UVALUE_FBinop fop fm v1 v2))
              (fun v1 v2 =>
                 translate _failure_UB_to_ExpE
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
        (* CB TODO: This is probably not what we want in the long term!

           There are a couple of points here:

           1. We do not want to use uvalue_to_dvalue
           2. We do not want to do picks instead of uvalue_to_dvalue (current situation)
           3. We do not want to use UVALUE_GetElementPtr

           For each of these points:

           1. This is bad because uvalue_to_dvalue is "partial". It
              raises an error when the uvalue given to it is not fully
              concrete already. Arguably most of the time we would
              want the arguments to GetElementPtr to be concrete,
              because nondeterministic addresses likely causes
              UB... But it might not, and for instance an index could
              reasonably be `0 * undef`
           2. We could concretize everything using `pick` events,
              which initially might seem like a good option. Things
              like `0 * undef` will go through without a hitch. BUT
              suppose r = GetElementPtr a i such that r ≈ {v1, v2},
              i.e., the result is nondeterministically one of v1 or
              v2. Then a store to r should raise UB, which is
              currently handled using the predicate for pick events:

              da <- trigger (pick ua (exists x, forall da, concretize ua da -> da = x)) ;;

              However, if we pick before calling store the address
              will be concrete at this point, and so UB will not be
              raised, the nondeterminism is collapsed too early :(.
           3. Using UVALUE_GetElementPtr to delay the evaluation of
              GetElementPtr until it's used. This would be ideal
              because it would keep the address nondeterministic and
              allow us to raise UB if the address to a store
              concretizes to two different addresses... But this is
              problematic because GEP is handled by memory events,
              which should be interpreted before pick events, so
              raising more when handling pick is :(.

           This may be something worth readdressing when we modify the
           memory model interface to take uvalues. The problem should,
           essentially, go away?

         *)
        | OP_GetElementPtr dt1 (dt2, ptrval) idxs =>
          vptr <- denote_exp (Some dt2) ptrval ;;
          vs <- map_monad (fun '(dt, index) => denote_exp (Some dt) index) idxs ;;

          let maybe_dvs := dvptr <- uvalue_to_dvalue vptr ;;
                           dvs <- map_monad uvalue_to_dvalue vs ;;
                           ret (dvptr, dvs)
          in

          match maybe_dvs with
          | inr (dvptr, dvs) => fmap dvalue_to_uvalue (trigger (GEP dt1 dvptr dvs))
          | inl _ =>
            (* Pick to get dvalues *)
            dvptr <- concretize_or_pick vptr True ;;
            dvs <- map_monad (fun v => concretize_or_pick v True) vs ;;
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

        | OP_Freeze (dt, e) =>
          uv <- denote_exp (Some dt) e ;;
          dv <- pick_your_poison dt uv;;
          ret (dvalue_to_uvalue dv)
        end.
  Arguments denote_exp _ : simpl nomatch.

  Definition denote_op (o:exp dtyp) : itree exp_E uvalue :=
    denote_exp None o.
  Arguments denote_op _ : simpl nomatch.

      (* An instruction has only side-effects, it therefore returns [unit] *)

      Definition denote_instr
                 (i: (instr_id * instr dtyp)): itree instr_E unit :=
        match i with
        (* Pure operations *)

        | (IId id, INSTR_Op op) =>
          dv <- translate exp_E_to_instr_E (denote_op op) ;;
          trigger (LocalWrite id dv)

        (* Allocation *)
        | (IId id, INSTR_Alloca dt _ _) =>
          dv <- trigger (Alloca dt);;
          trigger (LocalWrite id (dvalue_to_uvalue dv))

        (* Load *)
        | (IId id, INSTR_Load _ dt (du,ptr) _) =>
          (* debug ("Load: " ++ to_string dt);; *)
          ua <- translate exp_E_to_instr_E (denote_exp (Some du) ptr) ;;
          da <- concretize_or_pick ua True ;;
          match da with
          | DVALUE_Poison => raiseUB "Load from poisoned address."
          | _ => dv <- trigger (Load dt da);;
                (* debug ("Loading: " ++ to_string dv);; *)
                trigger (LocalWrite id dv)
          end

        (* Store *)
        | (IVoid _, INSTR_Store _ (dt, val) (du, ptr) _) =>
          uv <- translate exp_E_to_instr_E (denote_exp (Some dt) val) ;;
          dv <- concretize_or_pick uv True ;;
          ua <- translate exp_E_to_instr_E (denote_exp (Some du) ptr) ;;
          da <- pickUnique ua ;;
          match da with
          | DVALUE_Poison => raiseUB "Store to poisoned address."
          | _ => trigger (Store da dv)
          end

        | (_, INSTR_Store _ _ _ _) => raise "ILL-FORMED itree ERROR: Store to non-void ID"

        (* Call *)
        | (pt, INSTR_Call (dt, f) args) =>
          uvs <- map_monad (fun '(t, op) => (translate exp_E_to_instr_E (denote_exp (Some t) op))) args ;;
          returned_value <-
          match Intrinsics.intrinsic_exp f with
          | Some s =>
            dvs <- map_monad (fun uv => pickUnique uv) uvs ;;
            fmap dvalue_to_uvalue (trigger (Intrinsic dt s dvs))
          | None =>
            fv <- translate exp_E_to_instr_E (denote_exp None f) ;;
            (* debug ("Call to function: " ++ to_string f) ;; *)
            trigger (Call dt fv uvs)
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
          dv <- concretize_or_pick uv True ;; (* TODO, should this be unique? *)
          match dv with
          | DVALUE_I1 comparison_bit =>
            if eq comparison_bit one then
              ret (inl br1)
            else
              ret (inl br2)
          | DVALUE_Poison => raiseUB "Branching on poison."
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
      Definition denote_code (c: code dtyp): itree instr_E unit :=
        map_monad_ denote_instr c.

      (* A block ends with a terminator, it either jumps to another block,
         or returns a dynamic value *)
      Definition denote_block (b: block dtyp) : itree instr_E (block_id + uvalue) :=
        denote_code (blk_code b);;
        translate exp_E_to_instr_E (denote_terminator (snd (blk_term b))).

      (* YZ FIX: no need to push/pop, but do all the assignments afterward *)
      (* One needs to be careful when denoting phi-nodes: they all must
         be evaluated in the same environment.
         We therefore starts the denotation of a phi-node by pushing a
         local copy of the environment of the stack, that we pop back
         once we are finished evaluating the expression.
         We then bind the resulting value in the underlying environment.
       *)
      (* The argument [bid] is the identity of the block from which we are jumping.
         The argument [id_p] are the phi nodes of the block toward which we are jumping. *)
      Definition denote_phi (bid : block_id) (id_p : local_id * phi dtyp) : itree exp_E (local_id * uvalue) :=
        let '(id, Phi dt args) := id_p in
        match assoc RawIDOrd.eq_dec bid args with
        | Some op =>
          uv <- denote_exp (Some dt) op ;;
          ret (id,uv)
        | None => raise ("jump: phi node doesn't include block " ++ to_string bid)
        end.

      Definition denote_bks (bks: list _): block_id -> itree instr_E (block_id + uvalue) :=
        loop (C := ktree _)
             (fun (bid : block_id + block_id) =>
                match bid with
                | inl bid
                | inr bid =>
                  (* We lookup the block [bid] to be denoted *)
                  match find_block DynamicTypes.dtyp bks bid with
                  | None => ret (inr (inl bid))
                  | Some block =>
                    (* We denote the block *)
                    bd <- denote_block block;;
                    (* And set the phi-nodes of the new destination, if any *)
                    match bd with
                    | inr dv => ret (inr (inr dv))
                    | inl bid_target =>
                      match find_block DynamicTypes.dtyp bks bid_target with
                      | None => ret (inr (inl bid_target))
                      | Some block_target =>
                        dvs <- Util.map_monad
                                (fun x => translate exp_E_to_instr_E (denote_phi bid x))
                                (blk_phis block_target) ;;
                        Util.map_monad (fun '(id,dv) => trigger (LocalWrite id dv)) dvs;;
                        ret (inl bid_target)
                      end
                    end
                  end
                end).

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
         to the _Asm_ language introduced in the POPL paper on itrees.
       *)
      (*
        We actually might be able to denote open programs without sending things at the level
        of types, just by deciding internally to loop or not and not reflect the invariant
        in the type.
       *)
      Definition denote_cfg (f: cfg dtyp) : itree instr_E uvalue :=
        r <- denote_bks (blks _ f) (init _ f) ;;
        match r with
        | inl bid => raise ("Can't find block in denote_cfg " ++ to_string bid)
        | inr uv  => ret uv
        end.

      (* TODO : Move this somewhere else *)
      Fixpoint combine_lists_err {A B:Type} (l1:list A) (l2:list B) : err (list (A * B)) :=
        match l1, l2 with
        | [], [] => ret []
        | x::xs, y::ys =>
          l <- combine_lists_err xs ys ;;
            ret ((x,y)::l)
        | _, _ =>
          (* YZ: This should be a failure, but we first need to have a proper
          story to handle main arguments since at the moment we expect exactly
          argc and argv, and feed default values to them *)
          (* failwith "combine_lists_err: different length lists" *)
          ret []
        end.

      (* The denotation of an itree function is a coq function that takes
         a list of uvalues and returns the appropriate semantics. *)
      Definition function_denotation : Type :=
        list uvalue -> itree L0' uvalue.

      Definition denote_function (df:definition dtyp (cfg dtyp)) : function_denotation :=
        fun (args : list uvalue) =>
          (* We match the arguments variables to the inputs *)
          (* debug ("Denoting function " ++ to_string (dc_name (df_prototype df)) ++ " with args: " ++ to_string args ++ " against prototype: " ++ to_string (df_args df));; *)
          bs <- lift_err ret (combine_lists_err (df_args df) args) ;;
             (* generate the corresponding writes to the local stack frame *)
          trigger MemPush ;;
          trigger (StackPush (map (fun '(k,v) => (k, v)) bs)) ;;
          rv <- translate instr_E_to_L0' (denote_cfg (df_instrs df)) ;;
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
    - (List.map df_prototype (m_definitions CFG)) is the set of possible Entry Functions  (also internal calls)
 *)
      Definition lookup_defn {B} := (@assoc _ B (@dvalue_eq_dec)).

      (* YZ Note: we could have chosen to distinguish both kinds of calls in [denote_instr] *)
      Definition denote_mcfg
                 (fundefs:list (dvalue * function_denotation)) (dt : dtyp)
                 (f_value : uvalue) (args : list uvalue) : itree L0 uvalue :=
        @mrec CallE (ExternalCallE +' _)
              (fun T call =>
                 match call with
                 | Call dt fv args =>
                   dfv <- concretize_or_pick fv True ;; (* TODO, should this be unique? *)
                   match (lookup_defn dfv fundefs) with
                   | Some f_den => (* If the call is internal *)
                     f_den args
                   | None =>
                     dargs <- map_monad (fun uv => pickUnique uv) args ;;
                     fmap dvalue_to_uvalue (trigger (ExternalCall dt fv dargs))
                   end
                 end)
              _ (Call dt f_value args).

End Denotation.
