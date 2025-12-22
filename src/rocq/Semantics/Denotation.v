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

From Stdlib Require Import
     ZArith String List
     FSets.FMapWeakList
     Bool.Bool.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor
     EitherMonad
     Eqv.

From ITree Require Import
     ITree
     Interp.Recursion
     Events.Exception.

From Vellvm Require Import
     Numeric.Integers
     Numeric.Floats
     Utilities
     Utils.IntMaps
     Utils.InterpEither
     Syntax
     Semantics.VellvmIntegers
     Semantics.LLVMEvents
     Semantics.LLVMParams
     Semantics.MemoryParams
     Semantics.Memory.MemBytes
     Semantics.ConcretizationParams
     Semantics.IntrinsicsDefinitions
     Utils.ListUtil
     DynamicValues
     Handlers.Concretization
     Handlers.LLVMExceptions.

Require Import Ceres.Ceres.

Import Sum.
Import Subevent.
Import EqvNotation.
Import ListNotations.
Import MonadNotation.

Set Implicit Arguments.
Set Contextual Implicit.

Open Scope monad_scope.
Open Scope string_scope.
Open Scope N_scope.

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

Module Denotation (LP : LLVMParams) (MP : MemoryParams LP) (Byte : ByteModule LP.ADDR LP.IP LP.SIZEOF LP.Events MP.BYTE_IMPL) (CP : ConcretizationParams LP MP Byte).
  Import CP.
  Import CONC.
  Import MP.
  Import LP.
  Import Events.

  Definition dv_zero_initializer (t:dtyp) : err dvalue :=
    default_dvalue_of_dtyp t.

  (** ** Ident lookups
      Look-ups depend on the nature of the [ident], that may be local or global.
      In each case, we simply trigger the corresponding read event.
      Note: global maps contain [dvalue]s, while local maps contain [uvalue]s.
      We perform the conversion here.
   *)
  Definition lookup_id (i:ident) : itree lookup_E uvalue :=
    match i with
    | ID_Global x => dv <- trigger (GlobalRead x);; ret (dvalue_to_uvalue dv)
    | ID_Local x  => trigger (LocalRead x)
    end.

  (* Predicate testing whether a [dvalue] is equal to zero at its type *)
  Definition dvalue_is_zero (dv : dvalue) : Prop :=
    match dv with
    | @DVALUE_I sz x   => x = VellvmIntegers.zero
    | DVALUE_IPTR x    => x = IP.zero
    | DVALUE_Double x  => x = Float.zero
    | DVALUE_Float x   => x = Float32.zero
    | _               => False
    end.

  Definition dvalue_not_zero dv := ~ (dvalue_is_zero dv).

  (* A trivially concrete [uvalue] does not need to go through a pick event to get concretize.
     This function therefore either triggers [pick], or perform a direct cast.
     The value of this "optimization" is debatable. *)
  Definition concretize_or_pick {E : Type -> Type} `{PickE -< E} `{FailureE -< E} (uv : uvalue) : itree E dvalue :=
    if is_concrete uv
    then lift_err ret (uvalue_to_dvalue uv)
    else dv <- trigger (pick_uvalue uv);; ret (proj1_sig dv).

  (* Pick a possibly poison value, treating poison as nondeterminism.
     This is used for freeze. *)
  Definition pick_your_poison {E : Type -> Type} `{PickE -< E} `{FailureE -< E} (uv : uvalue) : itree E dvalue :=
    match uv with
    | UVALUE_Poison dt => concretize_or_pick (UVALUE_Undef dt)
    | _             => concretize_or_pick uv
    end.

  (* A version of concretize_or_pick which forces uniqueness *)
  Definition concretize_or_pick_unique {E : Type -> Type} `{PickE -< E} `{FailureE -< E} (uv : uvalue) : itree E dvalue
    :=
    if is_concrete uv
    then lift_err ret (uvalue_to_dvalue uv)
    else dv <- trigger (pick_unique_uvalue uv);; ret (proj1_sig dv).

  (* Concretize values that are trivially deterministic *)
  Definition concretize_if_no_undef_or_poison {M} `{Monad M} `{RAISE_ERROR M} `{RAISE_UB M} `{RAISE_OOM M} (uv : uvalue) : M uvalue
    := if contains_undef_or_poison uv
       then ret uv
       else
         (* Since this `uvalue` is deterministic it should not matter
            that we'll just pick a default uvalue for undef /
            poison... No non-determinism will be lost. *)
         dv <- concretize_uvalue uv;;
         ret (dvalue_to_uvalue dv).

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

  Fixpoint denote_exp' 
           (top:option dtyp) (o:exp dtyp) {struct o} : itree exp_E uvalue :=
    let eval_texp '(dt,ex) := denote_exp' (Some dt) ex
    in
    match o with

    (* The translation injects the [lookup_E] interface used by [lookup_id] to the ambient one *)
    | EXP_Ident i =>
      translate LU_to_exp (lookup_id i)

    | EXP_Integer x =>
      match top with
      | None                => raise ("denote_exp given untyped EXP_Integer")
      | Some (DTYPE_I bits) => fmap dvalue_to_uvalue (coerce_integer_to_int (Some bits) x)
      | Some DTYPE_IPTR     => fmap dvalue_to_uvalue (coerce_integer_to_int None x)
      | Some typ            => raise ("bad type for constant int: " ++ to_string typ)
      end

    | EXP_Float x =>
      match top with
      | None              => raise ("denote_exp given untyped EXP_Float")
      | Some DTYPE_Float  => ret (UVALUE_Float x)
      | _                 => raise ("bad type for constant float")
      end

    | EXP_Double x =>
      match top with
      | None              => raise ("denote_exp given untyped EXP_Double")
      | Some DTYPE_Double => ret (UVALUE_Double x)
      | _                 => raise ("bad type for constant double")
      end

    | EXP_Hex x =>
      match top with
      | None              => raise ("denote_exp given untyped EXP_Hex")
      | Some DTYPE_Float  => ret (UVALUE_Float (Float32.of_double x))
      | Some DTYPE_Double => ret (UVALUE_Double x)
      | _                 => raise ("bad type for constant hex float")
      end

    | EXP_Bool b =>
      match b with
      | true  => ret (@UVALUE_I 1 VellvmIntegers.one)
      | false => ret (@UVALUE_I 1 VellvmIntegers.zero)
      end

    | EXP_Null => ret (UVALUE_Addr ADDR.null)

    | EXP_Zero_initializer =>
      match top with
      | None   => raise ("denote_exp given untyped EXP_Zero_initializer")
      | Some t => lift_err ret (fmap dvalue_to_uvalue (dv_zero_initializer t))
      end

    | EXP_Cstring es =>
      vs <- map_monad eval_texp es ;;
      ret (UVALUE_Array (@DTYPE_I 8) vs)

    | EXP_Undef =>
      match top with
      | None   => raise ("denote_exp given untyped EXP_Undef")
      | Some t => ret (UVALUE_Undef t)
      end

    | EXP_Poison =>
      match top with
      | None   => raise ("denote_exp given untyped EXP_Poison")
      | Some t => ret (UVALUE_Poison t)
      end

    (* Question: should we do any typechecking for aggregate types here? *)
    (* Option 1: do no typechecking: *)
    | EXP_Struct es =>
      vs <- map_monad eval_texp es ;;
      ret (UVALUE_Struct vs)

    (* Option 2: do a little bit of typechecking *)
    | EXP_Packed_struct es =>
      match top with
      | None => raise ("denote_exp given untyped EXP_Struct")
      | Some (DTYPE_Packed_struct _) =>
        vs <- map_monad eval_texp es ;;
        ret (UVALUE_Packed_struct vs)
      | _ => raise ("bad type for VALUE_Packed_struct")
      end

    | EXP_Array t es =>
      vs <- map_monad eval_texp es ;;
      ret (UVALUE_Array t vs)

    | EXP_Vector t es =>
      vs <- map_monad eval_texp es ;;
      ret (UVALUE_Vector t vs)

    (* The semantics of operators is complicated by both uvalues and
           undefined behaviors.
           We denote each operands first, but the denotation of the operator itself
           depends on whether it may raise UB, and how.
     *)
    | OP_IBinop iop dt op1 op2 =>
      v1 <- denote_exp' (Some dt) op1 ;;
      v2 <- denote_exp' (Some dt) op2 ;;
      ret (UVALUE_IBinop iop v1 v2)

    | OP_ICmp samesign cmp dt op1 op2 =>
      v1 <- denote_exp' (Some dt) op1 ;;
      v2 <- denote_exp' (Some dt) op2 ;;
      ret (UVALUE_ICmp samesign cmp v1 v2)

    | OP_FBinop fop fm dt op1 op2 =>
      v1 <- denote_exp' (Some dt) op1 ;;
      v2 <- denote_exp' (Some dt) op2 ;;
      ret (UVALUE_FBinop fop fm v1 v2)

    | OP_FCmp fcmp dt op1 op2 =>
      v1 <- denote_exp' (Some dt) op1 ;;
      v2 <- denote_exp' (Some dt) op2 ;;
      ret (UVALUE_FCmp fcmp v1 v2)

    | OP_Conversion conv dt_from op dt_to =>
      v <- denote_exp' (Some dt_from) op ;;
      ret (UVALUE_Conversion conv dt_from v dt_to)

    | OP_GetElementPtr dt1 (dt2, ptrval) idxs =>
      vptr <- denote_exp' (Some dt2) ptrval ;;
      vs <- map_monad (fun '(dt, index) => denote_exp' (Some dt) index) idxs ;;
      ret (UVALUE_GetElementPtr dt1 vptr vs)

    | OP_ExtractElement (dt_vec, vecop) (dt_idx, idx) =>
        vec <- denote_exp' (Some dt_vec) vecop ;;
        idx <- denote_exp' (Some dt_idx) idx ;;
        ret (UVALUE_ExtractElement dt_vec vec idx)

    | OP_InsertElement (dt_vec, vecop) (dt_elt, eltop) (dt_idx, idx) =>
        vec <- denote_exp' (Some dt_vec) vecop ;;
        elt <- denote_exp' (Some dt_elt) eltop ;;
        idx <- denote_exp' (Some dt_idx) idx ;;
        ret (UVALUE_InsertElement dt_vec vec elt idx)

    | OP_ShuffleVector (dt_vec1, vecop1) (dt_vec2, vecop2) (dt_mask, idxmask) =>
        vec1 <- denote_exp' (Some dt_vec1) vecop1 ;;
        vec2 <- denote_exp' (Some dt_vec2) vecop2 ;;
        idxmask <- denote_exp' (Some dt_mask) idxmask;;
        ret (UVALUE_ShuffleVector dt_vec1 vec1 vec2 idxmask)

    | OP_ExtractValue (dt, str) idxs =>
        str <- denote_exp' (Some dt) str ;;
        ret (UVALUE_ExtractValue dt str idxs)

    | OP_InsertValue (dt_str, strop) (dt_elt, eltop) idxs =>
        str <- denote_exp' (Some dt_str) strop ;;
        elt <- denote_exp' (Some dt_elt) eltop ;;
        ret (UVALUE_InsertValue dt_str str dt_elt elt idxs)

    | OP_Select (dt, cnd) (dt1, op1) (dt2, op2) =>
        cnd <- denote_exp' (Some dt) cnd ;;
        v1  <- denote_exp' (Some dt1) op1 ;;
        v2  <- denote_exp' (Some dt2) op2 ;;
        ret (UVALUE_Select cnd v1 v2)

    | OP_Freeze (dt, e) =>
      uv <- denote_exp' (Some dt) e ;;
      dv <- pick_your_poison uv;;
      ret (dvalue_to_uvalue dv)

    | EXP_Asm _ _ _ _ template _ =>
        raise ("denote_exp encountered inlined asm template " ++ template)

    | EXP_Metadata md =>
        (* METADATA TODO - it isn't clear what the denotations should be *)
        match md with
        | METADATA_Null => ret (UVALUE_Addr ADDR.null)
        | METADATA_Id _ => ret UVALUE_None
        | METADATA_Const tv => eval_texp tv
        | METADATA_Node _ => ret UVALUE_None
        | METADATA_Pair _ _ => ret UVALUE_None
        | METADATA_Debug _ _ => ret UVALUE_None
        | METADATA_File_info _ => ret UVALUE_None
        end

    | EXP_Splat elt =>
        match top with
        | None => raise ("denote_exp given untyped EXP_Splat")
        | Some (DTYPE_Vector sz t) =>
            (* use the type from the splat elt *)
            v <- eval_texp elt ;;
            (* this could be very expensive if the vector is big *)
            ret (UVALUE_Vector t (List.repeat v (N.to_nat sz)))
        | Some _ => raise ("denote_exp given EXP_Splat with non-vector type")
        end
    end.

  Definition denote_exp (top:option dtyp) (o:exp dtyp) : itree exp_E uvalue
    := uv <- denote_exp' top o;;
       concretize_if_no_undef_or_poison uv.

  Arguments denote_exp _ _ : simpl nomatch.

  Definition denote_op (o:exp dtyp) : itree exp_E uvalue :=
    denote_exp None o.
  Arguments denote_op _ : simpl nomatch.


  (* TODO: it would be nice to generalize this, but I really need to
     care about where the exception event is *)
  Definition catch_llvm_exc_instr_E_h : IFun instr_E (fun R : Type => eitherT uvalue (itree instr_E) R).
    red.
    intros T e.
    refine
      (match e with
       | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 exc))))))) =>
           match exc with
           | LLVMExc x => mkEitherT (ret (inl x))
           end
       | _ => mkEitherT (r <- trigger e ;; ret (inr r))
       end).
  Defined.

  Definition catch_llvm_exc_L0_h : IFun L0 (fun R : Type => eitherT uvalue (itree L0) R).
    red.
    intros T e.
    refine
      (match e with
       | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 exc))))))) =>
           match exc with
           | LLVMExc x => mkEitherT (ret (inl x))
           end
       | _ => mkEitherT (r <- trigger e ;; ret (inr r))
       end).
  Defined.

  Definition catch_llvm_exc_L0'_h : IFun L0' (fun R : Type => eitherT uvalue (itree L0') R).
    red.
    intros T e.
    refine
      (match e with
       | inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inr1 (inl1 exc)))))))) =>
           match exc with
           | LLVMExc x => mkEitherT (ret (inl x))
           end
       | _ => mkEitherT (r <- trigger e ;; ret (inr r))
       end).
  Defined.

  Definition catch_llvm_exc_instr_E : itree instr_E ~> eitherT uvalue (itree instr_E)
      := interp_either catch_llvm_exc_instr_E_h.

  Definition catch_llvm_exc_L0 : itree L0 ~> eitherT uvalue (itree L0)
      := interp_either catch_llvm_exc_L0_h.

  Definition catch_llvm_exc_L0' : itree L0' ~> eitherT uvalue (itree L0')
      := interp_either catch_llvm_exc_L0'_h.

  Definition denote_cmpxchg id cpx : itree instr_E unit :=
    (* SAZ: This will have to be revisited when we have a truly concurrent semantics. *)
    let '(ptr_ty, ptr_val) := cpx.(c_ptr) in
    let '(cmp_ty, cmp_val) := cpx.(c_cmp) in
    let '(new_ty, new_val) := cpx.(c_new) in

    (* Check whether the comparison types agree.  LLVM IR requires them to be integer
           or pointer types (otherwise the IR is not well formed).  Vellvm checks that
           the types are the same, but doesn't check their specific type.
     *)
    if (dtyp_eq_dec cmp_ty new_ty) then
      
      (* evaluate the arguments to the instruction *)
      ptr_uv <- translate exp_to_instr (denote_exp (Some ptr_ty) ptr_val) ;;
      cmp_uv <- translate exp_to_instr (denote_exp' (Some cmp_ty) cmp_val) ;;
      new_uv <- translate exp_to_instr (denote_exp' (Some cmp_ty) new_val) ;;
      
      (* Perform the load - load addresses must be unique *)
      ptr_dv <- concretize_or_pick_unique ptr_uv;;
      loaded_uv <- trigger (Load cmp_ty ptr_dv);;

      (* Perform the comparison - again we have to concretize the results *)
      (* SAZ: not clear whether this comparison implies "samesign" or not *)
      dv <- concretize_or_pick_unique (UVALUE_ICmp false Eq loaded_uv cmp_uv);;
      match dv with
      | @DVALUE_I 1 comparison_bit =>
          if equ comparison_bit one then
            
            (* They compared as equal: perform the write to memory *)
            trigger (Store cmp_ty ptr_dv new_uv) ;;
            (* return a struct with the loaded value and "true" *)
            let ret_uv := UVALUE_Struct [loaded_uv; @UVALUE_I 1 one] in
            trigger (LocalWrite id ret_uv);;
            ret tt
          else
            (* They compared as distinct: do not perform the write to memory *)
            (* return a struct with the loaded value and "false" *)                
            let ret_uv := UVALUE_Struct [loaded_uv; @UVALUE_I 1 zero] in
            trigger (LocalWrite id ret_uv);;
            ret tt
      | DVALUE_Poison dt => raiseUB ("comparing poison in atomiccmpxchg.")
      | _ => raise ("Br got non-bool value")
      end
    else 
      raise ("Ill-typed atomiccmpxchg").


  (* Implement the atomic modify operations in terms of Vellvm uvalues.
     Note: Langref doesn't seem to specifiy whether the arithmetic operations should be treated
           as having (or not) the signed/wrapping flags activated.  Here we (arbitrarily?)
           set them to false.
  *)
  Definition denote_atomic_rmw_operation a_op (pv : uvalue) (val : uvalue) : itree instr_E uvalue :=
    match a_op with      
    | Axchg =>
        (* xchg: *ptr = val *)
        ret val   
    | Aadd =>
        (* add: *ptr = *ptr + val *)
        ret (UVALUE_IBinop (Add false false) pv val)
    | Asub =>
        (* sub: *ptr = *ptr - val *)
        ret (UVALUE_IBinop (Sub false false) pv val)
    | Aand =>
        (* and: *ptr = *ptr - val *)
        ret (UVALUE_IBinop And pv val)
    | Aor =>
        (* or: *ptr = *ptr | val *)
        ret (UVALUE_IBinop Or pv val)
    | Axor =>
        (* xor: *ptr = *ptr ^ val *)
        ret (UVALUE_IBinop Xor pv val)
    | Anand =>
        (* nand: *ptr = ~( *ptr & val ) *)
        match val with
        | UVALUE_I sz _ =>
            (* SAZ: Is this the best way to get a UValue with 0xFFFF..FFFF bit pattern? *)
            ret (UVALUE_IBinop (Sub false false)
                   (@UVALUE_I sz (@repr (@bit_int sz) _ (@max_unsigned (@bit_int sz) _)))
                   (UVALUE_IBinop And pv val))            
        | _ => raise ("atomicrmw nand of non-integer value")
        end
    | Afadd =>
        (* fadd: *ptr = *ptr + val (using floating point arithmetic) *)
        ret (UVALUE_FBinop FAdd [] pv val)
    | Afsub =>
        (* fsub: *ptr = *ptr - val (using floating point arithmetic) *)
        ret (UVALUE_FBinop FSub [] pv val)
    | Amax
    | Amin
    | Aumax
    | Aumin
    | Afmax
    | Afmin
    | Afmaximum
    | Afminimum
    | Auinc_wrap
    | Audec_wrap
    | Ausub_cond
    | Ausub_sat => raise ("Unsupported atomicrwm operation")
    end.
    
  
  Definition denote_atomicrmw id armw : itree instr_E unit :=
    let '(ptr_ty, ptr_val) := armw.(a_ptr) in
    let '(a_ty, a_val) := armw.(a_val) in
    let a_op := armw.(a_operation) in

    (* evaluate the arguments to the instruction *)
    ptr_uv <- translate exp_to_instr (denote_exp (Some ptr_ty) ptr_val) ;;
    a_uv <- translate exp_to_instr (denote_exp' (Some a_ty) a_val) ;;
    
    (* Perform the load - load addresses must be unique *)
    ptr_dv <- concretize_or_pick_unique ptr_uv;;
    loaded_uv <- trigger (Load a_ty ptr_dv);;

    stored_uv <- denote_atomic_rmw_operation a_op loaded_uv a_uv ;;

    (* Perform the store *)
    trigger (Store a_ty ptr_dv stored_uv) ;;
    
    (* The result is the original value loaded from ptr before the modification *)
    trigger (LocalWrite id loaded_uv);;
    ret tt.

  
  (* An instruction has only side-effects, it therefore returns [unit] *)
  Definition denote_instr
    (i: (instr_id * instr dtyp * list (metadata dtyp))) (varargs : option ADDR.addr) : itree instr_E unit :=
    let '(i, md) := i in
    (* The following two lines set up file location information. *)
    (* extract it from the metadata: *)
    let err_loc := location_error_string md in
    (* imperatively set the flag for printing of exceptions
       [set_loc] extracts in such a way as to change the behavior of [print_msg]
     *)
    let bogus := set_loc err_loc in
    let err_loc := (bogus ++ err_loc) in
    match i with
    (* Pure operations *)

    | (IId id, INSTR_Op op) =>
        uv <- translate exp_to_instr (denote_op op) ;;
        trigger (LocalWrite id uv) ;;
        ret tt
    (* Allocation *)
    | (IId id, INSTR_Alloca dt annotations) =>
        let num_elements :=
          match find
                  (fun x => match x with | ANN_num_elements _ => true | _ => false end)
                  annotations with
          | Some (ANN_num_elements n) => Some n
          | _ => None
          end
        in
        let align :=
          match find
                  (fun x => match x with | ANN_align _ => true | _ => false end)
                  annotations with
          | Some (ANN_align a) => Some a
          | _ => None
          end
        in
        match num_elements with
        | None =>
            dv <- trigger (Alloca dt 1 align);;
            trigger (LocalWrite id (dvalue_to_uvalue dv))
        | Some (t, num_exp) =>
            un <- translate exp_to_instr (denote_exp (Some t) num_exp);;
            n <- concretize_or_pick_unique un;;
            dv <- trigger (Alloca dt (Z.to_N (dvalue_int_unsigned n)) align);;
            trigger (LocalWrite id (dvalue_to_uvalue dv))
        end;;
        ret tt

    (* Load *)
    | (IId id, INSTR_Load dt (du,ptr) _) =>
      ua <- translate exp_to_instr (denote_exp (Some du) ptr);;
      (* Load addresses must be unique *)
      da <- concretize_or_pick_unique ua;;
      uv <- trigger (Load dt da);;
      trigger (LocalWrite id uv) ;;
      ret tt

    (* Store *)
    | (IVoid _, INSTR_Store (dt, val) (du, ptr) _) =>
      uv <- translate exp_to_instr (denote_exp (Some dt) val) ;;
      ua <- translate exp_to_instr (denote_exp (Some du) ptr) ;;
      (* Store addresses must be unique *)
      da <- concretize_or_pick_unique ua ;;
      match da with
      | DVALUE_Poison dt => raiseUB (err_loc ++ ": Store to poisoned address.")
      | _ => trigger (Store dt da uv)
      end;;
      ret tt

    | (_, INSTR_Store _ _ _) => raise (err_loc ++ ": ILL-FORMED itree ERROR: Store to non-void ID")

    (* Call *)
    (* TODO: technically operand bundles can affect semantics *)                                     
    | (pt, INSTR_Call (dt, f) args _ _) =>
      uvs <- map_monad (fun '(t, op) => (translate exp_to_instr (denote_exp (Some t) op))) (List.map fst args) ;;
      returned_value <-
        match intrinsic_exp f with
          (* TODO: look at whether these can be moved to IntrinsicsDefinitions.v *)
      | Some s =>
          if String.eqb s "llvm.va_start"
          then
            match args, varargs with
            | [ ((t, e), _) ], Some varargs =>
                ua <- translate exp_to_instr (denote_exp (Some t) e);;
                da <- concretize_or_pick_unique ua;;
                match da with
                | DVALUE_Poison dt => raiseUB ("Store to poisoned address.")
                | _ => trigger (Store DTYPE_Pointer da (UVALUE_Addr varargs));;
                      ret UVALUE_None
                end
            | _, _ => raise (err_loc ++ ": va_start invalid arguments")
            end
          else
            if String.eqb s "llvm.va_copy"
            then
              match args with
              | [((DTYPE_Pointer, exp_dest), _); ((DTYPE_Pointer, exp_src), _)] =>
                  usrc <- translate exp_to_instr (denote_exp (Some DTYPE_Pointer) exp_src);;
                  dsrc <- concretize_or_pick_unique usrc;;
                  udest <- translate exp_to_instr (denote_exp (Some DTYPE_Pointer) exp_dest);;
                  ddest <- concretize_or_pick_unique udest;;
                  vargs <- trigger (Load DTYPE_Pointer dsrc);;
                  trigger (Store DTYPE_Pointer ddest vargs);;
                  ret UVALUE_None
              | _ => raise (err_loc ++ ": va_copy invalid arguments")
              end
            else
              if String.eqb s "llvm.va_end"
              then ret UVALUE_None
              else dvs <- map_monad (fun uv => concretize_or_pick_unique uv) uvs;;
                   res <- trigger (Intrinsic dt s dvs);;
                   match res with
                   | inl exc => raiseLLVM exc
                   | inr dv => ret (dvalue_to_uvalue dv)
                   end
      | None =>
        fv <- translate exp_to_instr (denote_exp None f);;
        res <- trigger (Call dt fv uvs);;
        match res with
        | inl exc => raiseLLVM exc
        | inr uv => ret uv
        end
      end
      ;;
      match pt with
      | IVoid _ =>
          ret tt
      | IId id  =>
          trigger (LocalWrite id returned_value);;
          ret tt
      end

    | (IVoid _, INSTR_Comment _) => ret tt

    | (pt, INSTR_VAArg (t, ptr_to_args_exp) argty) =>
        uptr_to_args <- translate exp_to_instr (denote_exp (Some DTYPE_Pointer) ptr_to_args_exp);;
        ptr_to_args <- concretize_or_pick_unique uptr_to_args;;
        uargs <- trigger (Load DTYPE_Pointer ptr_to_args);;
        args <- concretize_or_pick_unique uargs;;
        retv <- trigger (Load argty args);;
        ix <- lift_OOM (IP.from_Z 1);;
        args' <- lift_err_oom_RAISE_ERROR_OOM (GEP.handle_gep argty args [DVALUE_IPTR ix]);;
        trigger (Store DTYPE_Pointer ptr_to_args (dvalue_to_uvalue args'));;
        match pt with
        | IVoid _ => ret tt
        | IId id  => trigger (LocalWrite id retv);;
                     ret tt
        end
          
    | (IId id, INSTR_AtomicCmpXchg cpx) =>
        denote_cmpxchg id cpx

    | (IId id, INSTR_AtomicRMW armw) =>
        denote_atomicrmw id armw
      (* TODO: revisit with a proper concurrenc model *)

    | (_, INSTR_Fence _ _) => ret tt
                       
    (* Currently unhandled itree instructions *)
    | (_, INSTR_LandingPad _ _ _) => raise (err_loc ++ ": Unsupported INSTR_Landingpad")
    (* Error states *)
    | (_, _) => raise (err_loc ++ ": ID / Instr mismatch void / non-void")
    end.

  (* Computes the label to be returned by a switch terminator, after evaluation of values
         assuming already neither poison nor undef for the selector *)
  Fixpoint select_switch
           (value : dvalue) (default_dest : block_id)
           (switches : list (dvalue * block_id)) : err block_id.
    refine
      (match switches with
       | [] => ret default_dest
       | (v,id):: switches =>
           match value, v with
           | @DVALUE_I sz1 i1, @DVALUE_I sz2 i2
             => _
           | _,_ => failwith "Ill-typed switch."
           end
       end).

    destruct (Pos.eq_dec sz1 sz2); subst.
    - exact (if VellvmIntegers.cmp Ceq i1 i2
             then ret id
             else select_switch value default_dest switches).
    - exact (failwith "Ill-typed switch.").
  Defined.

  (* A [terminator] either returns from a function call, producing a [dvalue],
         or jumps to a new [block_id]. *)

  Definition denote_terminator (trm: (instr_id * terminator dtyp * list (metadata dtyp))): itree instr_E (block_id + uvalue) :=
    let '(iid, t, md) := trm in
    let err_loc := location_error_string md in
    let bogus := set_loc err_loc in
    let err_loc := (bogus ++ err_loc) in
    match t with

    | TERM_Ret (dt, op) =>
      dv <- (translate exp_to_instr (denote_exp (Some dt) op)) ;;
      ret (inr dv)

    | TERM_Ret_void =>
        ret (inr UVALUE_None)

    | TERM_Br (dt,op) br1 br2 =>
      uv <- (translate exp_to_instr (denote_exp (Some dt) op)) ;;
      dv <- concretize_or_pick_unique uv;;
      match dv with
      | @DVALUE_I 1 comparison_bit =>
        if equ comparison_bit one then
          ret (inl br1)
        else
          ret (inl br2)
      | DVALUE_Poison dt => raiseUB (err_loc ++ ": Branching on poison.")
      | _ => raise (err_loc ++ ": Br got non-bool value")
      end

    | TERM_Br_1 br => ret (inl br)

    | TERM_Switch (dt,e) default_br dests =>
      uselector <- (translate exp_to_instr (denote_exp (Some dt) e));;
      (* Selection on [undef] is UB *)
      selector <- concretize_or_pick_unique uselector;;
      if dvalue_is_poison selector
      then raiseUB (err_loc ++ ": Switching on poison.")
      else (* We evaluate all the selectors. Note that they are enforced to be constants, we could reflect this in the syntax and avoid this step *)
        switches <- map_monad
                     (fun '((TInt_Literal sz x),id) =>
                        s <- (coerce_integer_to_int (Some sz) x);;
                        ret (s,id))
                     dests;;
        lift_err (fun b => ret (inl b)) (select_switch selector default_br switches)

    | TERM_Unreachable => raiseUB (err_loc ++ ": IMPOSSIBLE: unreachable in reachable position")

      (* TODO: technically operand bundles can affect the semantics of invoke *)
    | TERM_Invoke (dt, fnptrval) args to_label unwind_label anns _ =>
      uvs <- map_monad (fun '(t, op) => (translate exp_to_instr (denote_exp (Some t) op))) (List.map fst args) ;;
      fv <- (translate exp_to_instr (denote_exp None fnptrval)) ;;
      rv <- trigger (Call dt fv uvs) ;;
      (* branch to to_label *)
      match rv with
      | inl exc =>
          (* Exception case. Need to jump to unwind label *)
          (* TODO: Need to pass exception value to somewhere *)
          ret (inl unwind_label)
      | inr returned_value =>
          match iid with
          | IVoid _ => ret tt
          | IId id  => trigger (LocalWrite id returned_value)
          end;;
          ret (inl to_label)
      end

    | TERM_Resume (t, expr) => 
      exn <- translate exp_to_instr (denote_exp (Some t) expr);;
      raiseLLVM exn

    (* Currently unhandled VIR terminators *)
    | TERM_IndirectBr _ _ => raise (err_loc ++ ": Unsupport itree terminator")
    end.

  (* Denoting a list of instruction simply binds the trees together *)
  Definition denote_code (c: code dtyp) (varargs : option ADDR.addr) : itree instr_E unit :=
    map_monad_ (fun i => denote_instr i varargs) c.

  Definition denote_phi (bid_from : block_id) (id_p : local_id * phi dtyp * (list (metadata dtyp))) : itree exp_E (local_id * uvalue) :=
    let '(id, Phi dt args, md) := id_p in
    let err_loc := location_error_string md in
    let bogus := set_loc err_loc in
    let err_loc := (bogus ++ err_loc) in
    match assoc bid_from args with
    | Some op =>
      uv <- denote_exp (Some dt) op ;;
      ret (id,uv)
    | None => raise (err_loc ++ ": jump: phi node doesn't include block ")
    end.

  Definition denote_phis (bid_from: block_id) (phis: list (local_id * phi dtyp * (list (metadata dtyp)))): itree instr_E unit :=
    dvs <- map_monad
             (fun x => translate exp_to_instr (denote_phi bid_from x))
             phis;;
    map_monad (fun '(id,dv) => trigger (LocalWrite id dv)) dvs;;
    ret tt.

  (* A block ends with a terminator, it either jumps to another block,
         or returns a dynamic value *)
  Definition denote_block (b: block dtyp) (bid_from : block_id) (varargs : option ADDR.addr) : itree instr_E (block_id + uvalue) :=
    denote_phis bid_from (blk_phis b);;
    denote_code (blk_code b) varargs;;
    denote_terminator (blk_term b).

  (* Our denotation currently contains two kinds of indirections: jumps to labels, internal to
         a cfg, and calls to functions, that jump from a cfg to another.
         In order to denote a single [cfg], we tie the first knot by linking together all the blocks
         contain in the [cfg].
         Note that contrary to calls, no events have been explicitely introduced for internal jumps.
         This is due to the _tail recursive_ nature of these jumps: they only occur as the last
         instruction of blocks. We hence can use a [loop] operator to do the linking, as opposed
         to the more general [mrec] operator that will be used to link internal calls.

         The idea here is simply to enter the body through the [init] [block_id] of the [cfg].
         As long as the computation returns a new label to jump to, we feed it back to the loop.
         If it ever returns a dynamic value, we exit the loop by returning the [dvalue].
   *)
  Definition denote_ocfg (bks: ocfg dtyp) (varargs : option ADDR.addr)
    : (block_id * block_id) -> itree instr_E ((block_id * block_id) + uvalue) :=
    iter (C := ktree _) (bif := sum)
         (fun '((bid_from,bid_src) : block_id * block_id) =>
            match find_block bks bid_src with
            | None => ret (inr (inl (bid_from,bid_src)))
            | Some block_src =>
              bd <- denote_block block_src bid_from varargs;;
              match bd with
              | inr dv => ret (inr (inr dv))
              | inl bid_target => ret (inl (bid_src,bid_target))
              end
            end).

  Definition denote_cfg (f: cfg dtyp) (varargs : option ADDR.addr) : itree instr_E uvalue :=
    r <- denote_ocfg (blks f) varargs (init f,init f) ;;
    match r with
    | inl bid => raise ("Can't find block in denote_cfg " ++ to_string (snd bid))
    | inr uv  => ret uv
    end.

  (* The denotation of an itree function is a coq function that takes
         a list of uvalues and returns the appropriate semantics. *)
  Definition function_denotation : Type :=
    list uvalue -> itree L0' uvalue.

  Fixpoint combine_lists_varargs {A B:Type} (l1:list A) (l2:list B) : err (list (A * B) * list B) :=
    match l1, l2 with
    | [], [] => ret ([], [])
    | x::xs, y::ys =>
        '(l, vargs) <- combine_lists_varargs xs ys ;;
        ret ((x,y)::l, vargs)
    | _, [] =>
        failwith "combine_lists_varargs: too few arguments"
    | [], vargs =>
        ret ([], vargs)
    end.

  Definition pop_call_frame {E k v exc} `{MemoryE -< E} `{StackE k v exc -< E} : itree E unit :=
    trigger StackPop;;
    trigger MemPop.

  (* Push call frame, return varargs address *)
  Definition push_call_frame (df:definition dtyp (cfg dtyp)) (args : list uvalue) : itree L0' ADDR.addr :=
    (* We match the arguments variables to the inputs *)
    '(bs, vs) <- lift_err ret (combine_lists_varargs (df_args df) args) ;;
    dts <- lift_err ret (map_monad dtyp_of_uvalue_fun vs);;
    let dt := DTYPE_Packed_struct dts in
    (* generate the corresponding writes to the local stack frame *)
    trigger MemPush ;;
    trigger (StackPush bs) ;;
    varargs <- trigger (Alloca dt 1 None);;
    trigger (Store dt varargs (UVALUE_Packed_struct vs));;
    match varargs with
    | DVALUE_Addr varg =>
        ret varg
    | _ => raise "Non-address returned from alloca of varargs"
    end.

  Definition denote_function (df:definition dtyp (cfg dtyp)) : function_denotation :=
    fun (args : list uvalue) =>
      varg <- push_call_frame df args;;
      rv <- translate instr_to_L0' (denote_cfg (df_instrs df) (Some varg));;
      pop_call_frame;;
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

  Definition lookup_defn (dv : dvalue) (m : IntMap function_denotation) : option function_denotation
    := match dv with
       | DVALUE_Addr addr =>
           lookup (PTOI.ptr_to_int addr) m
       | _ => None
       end.

  Definition denote_mcfg
    (fundefs:IntMap function_denotation) (dt : dtyp)
    (f_value : uvalue) (args : list uvalue) : itree L0 (uvalue + uvalue) :=
    @mrec CallE (ExternalCallE +' _)
      (fun T call =>
         match call with
         | Call dt fv args =>
             dfv <- concretize_or_pick fv;;
             match (lookup_defn dfv fundefs) with
             | Some f_den => (* If the call is internal *)
                 unEitherT (catch_llvm_exc_L0' (f_den args))
             | None =>
                 dargs <- map_monad (fun uv => concretize_or_pick_unique uv) args ;;
                 fmap inr (fmap dvalue_to_uvalue (trigger (ExternalCall dt fv dargs)))
             end
         end)
      _ (Call dt f_value args).
End Denotation.
