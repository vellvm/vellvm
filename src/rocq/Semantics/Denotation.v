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
  FSets.FMapWeakList
  Bool.Bool.

From ITree Require Import
  ITree
  Interp.Recursion
  Events.Exception.

From Vellvm Require Import
  Numeric.Integers
  Numeric.Floats
  Utils.Assoc
  Utilities
  Syntax
  Semantics.VellvmIntegers
  Semantics.VellvmFloats
  Semantics.LLVMEvents
  Semantics.LLVMParams
  Semantics.Operations
  Semantics.IntrinsicsDefinitions
  Semantics.DynamicValues.

From QuickChick Require Import Show.

Import Sum.
Import Subevent.

Open Scope string_scope.
Open Scope N_scope.

(* end hide *)

(* See src/ml/Extract.v for the special handling of these operation. *)
Record fast_mode := mk_fast_mode {
                        fast_mode_set : bool -> unit ;
                        fast_mode_get : unit -> bool ;
                      }.

Definition fast_mode_object : fast_mode :=
  mk_fast_mode (fun (_:bool) => tt) (fun (_:unit) => false).

(* TODO: define notations to hide trigger *)
(* TODO: Should lift from EOB to itree be a coercion? *)
(* TODO: Reconsider minimizing the number of translations? *)

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

Module Denotation (LP : LLVMParams).
  Module Ops := Operations.Operations LP.
  Import Ops.
  Import GEP SELECT COMPARE MBYTES CONVERT.
  Import LP LP.DV.
  
  Definition dv_zero_initializer (t:dtyp) : EOB dvalue :=
    default_dvalue_of_dtyp t.
  
  (** ** Ident lookups
      Look-ups depend on the nature of the [ident], that may be local or global.
      In each case, we simply trigger the corresponding read event.
      Note: global maps contain [dvalue]s, while local maps contain [uvalue]s.
      We perform the conversion here.
   *)
  Definition lookup_id (i:ident) : itree (lookup_E dvalue) dvalue :=
    match i with
    | ID_Global x => trigger (GlobalRead x)
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

  Definition denote_int_syntax (x:int_syntax) : Z := 
    BinIntDef.Z.of_num_int x.

  (* TODO: cleanup with typeclasses *)
  Definition denote_float_syntax_as_float32 (f:float_syntax) : option float32 :=
    float32_of_float_syntax f.
    
  Definition denote_float_syntax_as_float (f:float_syntax) : option float := 
    float_of_float_syntax f.

  Definition lift {E} `{FailureE -< E} `{OOME -< E} `{UBE -< E} :
    EOB ~> itree E :=
    fun _ x => match x with
            | raise_error s => raise s
            | raise_oom   s => raiseOOM s
            | raise_ub    s => raiseUB s
            | raise_ret   v => ret v
            end.

  Definition freeze {E} `{DrawE -< E} (dv : dvalue) : itree E dvalue :=
    match dv with
    | DVALUE_Poison dt => trigger (draw dt)
    | _ => ret dv
    end.
  
  Fixpoint denote_exp'
    (top:option dtyp) (o:exp dtyp) {struct o} : itree (exp_E dvalue) dvalue :=
    let eval_texp '(dt,ex) := denote_exp' (Some dt) ex
    in
    match o with

    (* The translation injects the [lookup_E] interface used by [lookup_id] to the ambient one *)
    | EXP_Ident i =>
      translate (@LU_to_exp dvalue) (lookup_id i)
                
    | EXP_Integer x =>
        match top with
        | None                => raise ("denote_exp given untyped EXP_Integer")
        | Some (DTYPE_I bits) => lift (coerce_integer_to_int (Some bits) (denote_int_syntax x))
        | Some DTYPE_IPTR     => lift (coerce_integer_to_int None (denote_int_syntax x))
        | Some typ            => raise ("bad type for constant int: " ++ show typ)
        end

    (* TODO: define a typeclass for handling all floating point representations *)
    | EXP_Float x =>
        match top with
        | None                      => raise ("denote_exp given untyped EXP_Float")
        | Some (DTYPE_FP FP_float)  =>
            match denote_float_syntax_as_float32 x with
            | Some f => ret (DVALUE_Float f)
            | None => raise ("bad float literal")
            end
        | Some (DTYPE_FP FP_double) =>
            match denote_float_syntax_as_float x with
            | Some f => ret (DVALUE_Double f)
            | None => raise ("bad double literal")
            end
        | Some (DTYPE_FP _)        => raise ("unsupported float type")
        | _                        => raise ("bad type for constant float")
        end

    | EXP_Bool b =>
      match b with
      | true  => ret (@DVALUE_I 1 VellvmIntegers.one)
      | false => ret (@DVALUE_I 1 VellvmIntegers.zero)
      end
 
    | EXP_Null => ret (DVALUE_Addr ADDR.null)
                     
    | EXP_Zero_initializer =>
      match top with
      | None   => raise ("denote_exp given untyped EXP_Zero_initializer")
      | Some t => lift (dv_zero_initializer t)
      end

    | EXP_Cstring es =>
      vs <- map_monad eval_texp es ;;
      ret (DVALUE_Array (@DTYPE_I 8) vs)

    | EXP_Poison =>
        match top with
        | None   => raise ("denote_exp given untyped EXP_Poison")
        | Some t => ret (DVALUE_Poison t)
        end

    (* Question: should we do any typechecking for aggregate types here? *)
    (* Option 1: do no typechecking: *)
    | EXP_Struct es =>
        vs <- map_monad eval_texp es ;;
        ret (DVALUE_Struct vs)

    (* Option 2: do a little bit of typechecking *)
    | EXP_Packed_struct es =>
        match top with
        | None => raise ("denote_exp given untyped EXP_Struct")
        | Some (DTYPE_Packed_struct _) =>
            vs <- map_monad eval_texp es ;;
            ret (DVALUE_Packed_struct vs)
        | _ => raise ("bad type for VALUE_Packed_struct")
        end

    | EXP_Array t es =>
      vs <- map_monad eval_texp es ;;
      ret (DVALUE_Array t vs)

    | EXP_Vector t es =>
      vs <- map_monad eval_texp es ;;
      ret (DVALUE_Vector t vs)
          
    (* The semantics of operators is complicated by both uvalues and undefined behaviors.
           We denote each operands first, but the denotation of the operator itself
           depends on whether it may raise UB, and how.
     *)
    | OP_IBinop iop dt op1 op2 =>
      v1 <- denote_exp' (Some dt) op1 ;;
      v2 <- denote_exp' (Some dt) op2 ;;
      lift (eval_iop iop v1 v2)

    | OP_ICmp samesign cmp dt op1 op2 =>
        v1 <- denote_exp' (Some dt) op1 ;;
        v2 <- denote_exp' (Some dt) op2 ;;
        lift (eval_icmp samesign cmp v1 v2)

    (* TODO: fast_math? *)                
    | OP_FBinop fop _ dt op1 op2 =>
        v1 <- denote_exp' (Some dt) op1 ;;
        v2 <- denote_exp' (Some dt) op2 ;;
        lift (eval_fop fop v1 v2)
             
    (* TODO: fast_math? **)
    | OP_Fneg _ (dt, op) =>
        v <- denote_exp' (Some dt) op ;;
        lift (eval_fneg v)
             
    | OP_FCmp fcmp dt op1 op2 =>
        v1 <- denote_exp' (Some dt) op1 ;;
        v2 <- denote_exp' (Some dt) op2 ;;
        lift (eval_fcmp fcmp v1 v2)

    | OP_Conversion conv dt_from op dt_to =>
        v <- denote_exp' (Some dt_from) op ;;
        lift (convert conv dt_from v dt_to)

    | OP_GetElementPtr dt1 (dt2, ptrval) idxs =>
        vptr <- denote_exp' (Some dt2) ptrval ;;
        vs <- map_monad (fun '(dt, index) => denote_exp' (Some dt) index) idxs ;;
        lift (eval_gep dt1 vptr vs)

     | OP_ExtractElement (dt_vec, vecop) (dt_idx, idx) =>
        vec <- denote_exp' (Some dt_vec) vecop ;;
        idx <- denote_exp' (Some dt_idx) idx ;;
        elt_typ <- match dt_vec with
                      | DTYPE_Vector _ t => ret t
                      | _ => raise "Invalid vector type for ExtractElement"
                  end;;
        lift (index_into_vec_dv elt_typ vec idx)

    | OP_InsertElement (dt_vec, vecop) (dt_elt, eltop) (dt_idx, idx) =>
        vec <- denote_exp' (Some dt_vec) vecop ;;
        elt <- denote_exp' (Some dt_elt) eltop ;;
        idx <- denote_exp' (Some dt_idx) idx ;;
        lift (insert_into_vec_dv dt_vec vec elt idx)

    | OP_ShuffleVector (dt_vec1, vecop1) (dt_vec2, vecop2) (dt_mask, idxmask) =>
        vec1 <- denote_exp' (Some dt_vec1) vecop1 ;;
        vec2 <- denote_exp' (Some dt_vec2) vecop2 ;;
        idxmask <- denote_exp' (Some dt_mask) idxmask;;
        raise ("todo: implement shuffle_vector" )
        (* ret (UVALUE_ShuffleVector dt_vec1 vec1 vec2 idxmask) *)

    | OP_ExtractValue (dt, str) idxs =>
        str <- denote_exp' (Some dt) str ;;
        (* Should this be pulled out into a definition? *)
        let fix loop str idxs : EOB dvalue :=
          match idxs with
          | [] => ret str
          | i :: tl =>
              v <- index_into_str_dv str i ;;
              loop v tl
          end
        in
        lift (loop str (List.map denote_int_syntax idxs))

    | OP_InsertValue (dt_str, strop) (dt_elt, eltop) idxs =>
        str <- denote_exp' (Some dt_str) strop ;;
        elt <- denote_exp' (Some dt_elt) eltop ;;
        let fix loop str idxs : EOB dvalue :=
          match idxs with
          | [] => raise_error "Index was not provided"
          | i :: nil =>
              insert_into_str str elt i
          | i :: tl =>
              subfield <- index_into_str_dv str i;;
              modified_subfield <- loop subfield tl;;
              insert_into_str str modified_subfield i
          end in
        lift (loop str (List.map denote_int_syntax idxs))

    | OP_Select (dt, cnd) (dt1, op1) (dt2, op2) =>
        dcond <- denote_exp' (Some dt) cnd ;;
        v1    <- denote_exp' (Some dt1) op1 ;;
        v2    <- denote_exp' (Some dt2) op2 ;;
        lift (eval_select dcond v1 v2)

    | EXP_Metadata md =>
        (* METADATA TODO - it isn't clear what the denotations should be *)
        match md with
        | METADATA_Null => ret (DVALUE_Addr ADDR.null)
        | METADATA_Id _ => ret DVALUE_None
        | METADATA_Const tv => eval_texp tv
        | METADATA_Node _ => ret DVALUE_None
        | METADATA_Pair _ _ => ret DVALUE_None
        | METADATA_Debug _ _ => ret DVALUE_None
        | METADATA_File_info _ => ret DVALUE_None
        end

    | EXP_Asm _ _ _ _ template _ =>
        raise ("denote_exp encountered inlined asm template " ++ template)

    | EXP_Splat elt =>
        match top with
        | None => raise ("denote_exp given untyped EXP_Splat")
        | Some (DTYPE_Vector sz t) =>
            (* use the type from the splat elt *)
            v <- eval_texp elt ;;
            (* this could be very expensive if the vector is big *)
            ret (DVALUE_Vector t (List.repeat v (N.to_nat sz)))
        | Some _ => raise ("denote_exp given EXP_Splat with non-vector type")
        end
          
    | OP_Freeze (dt, e) =>
        dv <- denote_exp' (Some dt) e ;;
        freeze dv
    end.

  Definition denote_exp (top:option dtyp) (o:exp dtyp) : itree (exp_E dvalue) dvalue
    := denote_exp' top o.
  Arguments denote_exp _ _ : simpl nomatch.

  Definition denote_op (o:exp dtyp) : itree (exp_E dvalue) dvalue :=
    denote_exp None o.
  Arguments denote_op _ : simpl nomatch.

  Definition local_write {E} `{LocalE raw_id dvalue -< E}
    (id : raw_id) (dv : dvalue) : itree E unit :=
    trigger (LocalWrite id dv).

  Definition denote_cmpxchg (id : raw_id) (cpx : cmpxchg dtyp) : itree (instr_E dvalue) unit :=
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
      ptr_v <- translate (@exp_to_instr dvalue) (denote_exp (Some ptr_ty) ptr_val) ;;
      cmp_v <- translate (@exp_to_instr dvalue) (denote_exp' (Some cmp_ty) cmp_val) ;;
      new_v <- translate (@exp_to_instr dvalue) (denote_exp' (Some cmp_ty) new_val) ;;

      (* Perform the load *)
      loaded_v <- trigger (Load cmp_ty ptr_v);;
      (* Perform the comparison *)
      (* SAZ: not clear whether this comparison implies "samesign" or not *)
      dv <- lift (eval_icmp false Eq loaded_v cmp_v);;
      match dv with
      (* TODO: Shouldn't the size argument be explicit? *)
      | @DVALUE_I 1 comparison_bit =>
          if equ comparison_bit one then
            (* They compared as equal: perform the write to memory *)
            trigger (Store cmp_ty ptr_v new_v) ;;
            (* return a struct with the loaded value and "true" *)
            let ret_v := DVALUE_Struct [loaded_v; @DVALUE_I 1 one] in
            local_write id ret_v
          else
            (* They compared as distinct: do not perform the write to memory *)
            (* return a struct with the loaded value and "false" *)
            let ret_v := DVALUE_Struct [loaded_v; @DVALUE_I 1 zero] in
            local_write id ret_v
      | DVALUE_Poison dt => raiseUB ("comparing poison in atomiccmpxchg.")
      | _ => raise ("Br got non-bool value")
      end
    else
      raise ("Ill-typed atomiccmpxchg").
                       
  (* Implement the atomic modify operations in terms of Vellvm uvalues.
     Note: Langref doesn't seem to specifiy whether the arithmetic operations should be treated
           as having (or not) the signed/wrapping flags activated.  Here we (arbitrarily?)
           set them to false.
           Similarly, it does not state whether the `disjoint` flag for `or` can be applied,
           so we set it to false.
  *)
  Definition denote_atomic_rmw_operation a_op (pv : dvalue) (val : dvalue) : itree (instr_E dvalue) dvalue :=
    match a_op with
    | Axchg =>
        (* xchg: *ptr = val *)
        ret val
    | Aadd =>
        (* add: *ptr = *ptr + val *)
        lift (eval_iop (Add false false) pv val)
    | Asub =>
        (* sub: *ptr = *ptr - val *)
        lift (eval_iop (Sub false false) pv val)
    | Aand =>
        (* and: *ptr = *ptr - val *)
        lift (eval_iop And pv val)
    | Aor =>
        (* or: *ptr = *ptr | val *)
        lift (eval_iop (Or false) pv val)
    | Axor =>
        (* xor: *ptr = *ptr ^ val *)
        lift (eval_iop Xor pv val)
    | Anand =>
        (* nand: *ptr = ~( *ptr & val ) *)
        match val with
        | DVALUE_I sz _ =>
            (* SAZ: Is this the best way to get a UValue with 0xFFFF..FFFF bit pattern? *)
            (* YZ: Same question, but over dvalues *)
            lift
              (and_v <- eval_iop And pv val;;
               eval_iop (Sub false false) (@DVALUE_I sz (@repr (@bit_int sz) _ (@max_unsigned (@bit_int sz) _))) and_v)
        | _ => raise ("atomicrmw nand of non-integer value")
        end
    | Afadd =>
        (* fadd: *ptr = *ptr + val (using floating point arithmetic) *)
        lift (eval_fop FAdd pv val)
    | Afsub =>
        (* fsub: *ptr = *ptr - val (using floating point arithmetic) *)
        lift (eval_fop FSub pv val)
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

  Definition denote_atomicrmw id armw : itree (instr_E dvalue) unit :=
    let '(ptr_ty, ptr_val) := armw.(a_ptr) in
    let '(a_ty, a_val) := armw.(a_val) in
    let a_op := armw.(a_operation) in

    (* evaluate the arguments to the instruction *)
    ptr_v <- translate (@exp_to_instr dvalue) (denote_exp (Some ptr_ty) ptr_val) ;;
    a_v <- translate (@exp_to_instr dvalue) (denote_exp' (Some a_ty) a_val) ;;

    (* Perform the load - load addresses must be unique *)
    loaded_v <- trigger (Load a_ty ptr_v);;

    stored_v <- denote_atomic_rmw_operation a_op loaded_v a_v ;;

    (* Perform the store *)
    trigger (Store a_ty ptr_v stored_v) ;;

    (* The result is the original value loaded from ptr before the modification *)
    local_write id loaded_v;;
    ret tt.
  
  (* TODO: Maybe reverse the order in the pair we match on so that
     we don't have to analyse on the id when irrelavant to the semantics?
   *)
  (* An instruction has only side-effects, it therefore returns [unit] *)
  Definition denote_instr
    (i: (instr_id * instr dtyp * list (metadata dtyp))) (varargs : option ADDR.addr) : itree (instr_E dvalue) unit :=
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
        uv <- translate (@exp_to_instr dvalue) (denote_op op) ;;
        local_write id uv ;;
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
          | Some (ANN_align a) => Some (denote_int_syntax a)
          | _ => None
          end
        in
        match num_elements with
        | None =>
            v <- trigger (Alloca dt 1 align);;
            local_write id v
        | Some (t, num_exp) =>
            n <- translate (@exp_to_instr dvalue) (denote_exp (Some t) num_exp);;
            v <- trigger (Alloca dt (Z.to_N (dvalue_int_unsigned n)) align);;
            local_write id v
        end;;
        ret tt

    (* Load *)
    | (IId id, INSTR_Load dt (du,ptr) _) =>
      a <- translate (@exp_to_instr dvalue)  (denote_exp (Some du) ptr);;
      (* Load addresses must be unique *)
      v <- trigger (Load dt a);;
      local_write id v

    (* Store *)
    | (IVoid _, INSTR_Store (dt, val) (du, ptr) _) =>
      v <- translate (@exp_to_instr dvalue)  (denote_exp (Some dt) val) ;;
      a <- translate (@exp_to_instr dvalue)  (denote_exp (Some du) ptr) ;;
      (* Store addresses must be unique *)
      match a with
      | DVALUE_Poison dt => raiseUB (err_loc ++ ": Store to poisoned address.")
      | _ => trigger (Store dt a v)
      end;;
      ret tt

    | (_, INSTR_Store _ _ _) => raise (err_loc ++ ": ILL-FORMED itree ERROR: Store to non-void ID")

    (* Call *)
    (* TODO: technically operand bundles can affect semantics *)
    (* TODO: This should not be so complex, need to pull some code out *) 
    | (pt, INSTR_Call (dt, f) args _ _) =>
        vs <- map_monad (fun '(t, op) => (translate (@exp_to_instr dvalue) (denote_exp (Some t) op))) (List.map fst args) ;;
        returned_value <-
          match intrinsic_exp f with
          (* TODO: look at whether these can be moved to IntrinsicsDefinitions.v *)
          | Some s =>
              if String.eqb s "llvm.va_start"
              then
                match args, varargs with
                | [ ((t, e), _) ], Some varargs =>
                    a <- translate (@exp_to_instr dvalue) (denote_exp (Some t) e);;
                    match a with
                    | DVALUE_Poison dt => raiseUB ("Store to poisoned address.")
                    | _ => trigger (Store DTYPE_Pointer a (DVALUE_Addr varargs));;
                          ret DVALUE_None
                    end
                | _, _ => raise (err_loc ++ ": va_start invalid arguments")
                end
                  
              else
                if String.eqb s "llvm.va_copy"
                then
                  match args with
                  | [((DTYPE_Pointer, exp_dest), _); ((DTYPE_Pointer, exp_src), _)] =>
                      src <- translate (@exp_to_instr dvalue) (denote_exp (Some DTYPE_Pointer) exp_src);;
                      dest <- translate (@exp_to_instr dvalue)  (denote_exp (Some DTYPE_Pointer) exp_dest);;
                      vargs <- trigger (Load DTYPE_Pointer src);;
                      trigger (Store DTYPE_Pointer dest vargs);;
                      ret DVALUE_None
                  | _ => raise (err_loc ++ ": va_copy invalid arguments")
                  end
                else
                  if String.eqb s "llvm.va_end"
                  then ret DVALUE_None
                  else (* TODO: replug in the possibility for intrinsics to raise exceptions *)
                    trigger (Intrinsic dt s vs)
                      (* match res with *)
                      (* | inl exc => raiseLLVM exc *)
                      (* | inr dv => ret dv *)
                      (* end *)
                      
          | None =>
              fv <- translate (@exp_to_instr dvalue) (denote_exp None f);;
              trigger (Call dt fv vs)
              (* TODO: Exceptions handling *)
              (* res <- trigger (Call dt fv uvs);; *)
              (* match res with *)
              (* | inl exc => raiseLLVM exc *)
              (* | inr uv => ret uv *)
              (* end *)
          end
        ;;
        match pt with
        | IVoid _ =>
            ret tt
        | IId id  =>
            local_write id returned_value
        end

    | (IVoid _, INSTR_Comment _) => ret tt

    | (pt, INSTR_VAArg (t, ptr_to_args_exp) argty) =>
        ptr_to_args <- translate (@exp_to_instr dvalue) (denote_exp (Some DTYPE_Pointer) ptr_to_args_exp);;
        args <- trigger (Load DTYPE_Pointer ptr_to_args);;
        retv <- trigger (Load argty args);;
        ix <- lift (IP.from_Z 1);;
        args' <- lift (eval_gep argty args [DVALUE_IPTR ix]);;
        trigger (Store DTYPE_Pointer ptr_to_args args');;
        match pt with
        | IVoid _ => ret tt
        | IId id  => local_write id retv
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
           (switches : list (dvalue * block_id)) : EOB block_id.
    refine
      (match switches with
       | [] => ret default_dest
       | (v,id):: switches =>
           match value, v with
           | @DVALUE_I sz1 i1, @DVALUE_I sz2 i2
             => _
           | _,_ => raise_error "Ill-typed switch."
           end
       end).

    destruct (Pos.eq_dec sz1 sz2); subst.
    - exact (if VellvmIntegers.cmp Ceq i1 i2
             then ret id
             else select_switch value default_dest switches).
    - exact (raise_error "Ill-typed switch.").
  Defined.

  (* A [terminator] either returns from a function call, producing a [dvalue],
         or jumps to a new [block_id]. *)

  Definition denote_terminator
    (trm: (instr_id * terminator dtyp * list (metadata dtyp))) : itree (instr_E dvalue) (block_id + dvalue) :=
    let '(iid, t, md) := trm in
    let err_loc := location_error_string md in
    let bogus := set_loc err_loc in
    let err_loc := (bogus ++ err_loc) in
    match t with

    | TERM_Ret (dt, op) =>
      dv <- (translate (@exp_to_instr dvalue)  (denote_exp (Some dt) op)) ;;
      ret (inr dv)

    | TERM_Ret_void =>
        ret (inr DVALUE_None)

    | TERM_Br (dt,op) br1 br2 =>
      v <- (translate (@exp_to_instr dvalue)  (denote_exp (Some dt) op)) ;;
      match v with
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
      selector <- (translate (@exp_to_instr dvalue)  (denote_exp (Some dt) e));;
      (* Selection on [undef] is UB *)
      if dvalue_is_poison selector
      then raiseUB (err_loc ++ ": Switching on poison.")
      else (* We evaluate all the selectors. Note that they are enforced to be constants, we could reflect this in the syntax and avoid this step *)
        switches <- map_monad
                     (fun '((TInt_Literal sz x),id) =>
                        s <- lift (coerce_integer_to_int (Some sz) (denote_int_syntax x));;
                        ret (s,id))
                     dests;; 
        inl <$> lift (select_switch selector default_br switches)

    | TERM_Unreachable => raiseUB (err_loc ++ ": IMPOSSIBLE: unreachable in reachable position")

      (* TODO: technically operand bundles can affect the semantics of invoke *)
    | TERM_Invoke (dt, fnptrval) args to_label unwind_label anns _ =>
      uvs <- map_monad (fun '(t, op) => (translate (@exp_to_instr dvalue)  (denote_exp (Some t) op))) (List.map fst args) ;;
      fv <- (translate (@exp_to_instr dvalue)  (denote_exp None fnptrval)) ;;
      returned_value <- trigger (Call dt fv uvs) ;;
      (* branch to to_label *)
      match iid with
      | IVoid _ => ret tt
      | IId id  => local_write id returned_value
      end;;
      ret (inl to_label)
          
      (* (* TODO: replug exceptions *)  *)
      (* match rv with *)
      (* | inl exc => *)
      (*     (* Exception case. Need to jump to unwind label *) *)
      (*     (* TODO: Need to pass exception value to somewhere *) *)
      (*     ret (inl unwind_label) *)
      (* | inr returned_value => *)
      (*     match iid with *)
      (*     | IVoid _ => ret tt *)
      (*     | IId id  => local_write id returned_value *)
      (*     end;; *)
      (*     ret (inl to_label) *)
      (* end *)

    | TERM_Resume (t, expr) =>
      exn <- translate (@exp_to_instr dvalue)  (denote_exp (Some t) expr);;
      raiseLLVM exn

    (* Currently unhandled VIR terminators *)
    | TERM_IndirectBr _ _ => raise (err_loc ++ ": Unsupport itree terminator")
    end.

  (* Denoting a list of instruction simply binds the trees together *)
  Definition denote_code (c: code dtyp) (varargs : option ADDR.addr) : itree (instr_E dvalue) unit :=
    map_monad_ (fun i => denote_instr i varargs) c.

   Definition denote_phi (bid_from : block_id) (id_p : local_id * phi dtyp * (list (metadata dtyp))) : itree (exp_E dvalue) (local_id * dvalue) :=
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

  Definition denote_phis (bid_from: block_id) (phis: list (local_id * phi dtyp * (list (metadata dtyp)))): itree (instr_E dvalue) unit :=
    dvs <- map_monad
             (fun x => translate (@exp_to_instr dvalue) (denote_phi bid_from x))
             phis;;
    map_monad (fun '(id,dv) => local_write id dv) dvs;;
    ret tt.

  (* A block ends with a terminator, it either jumps to another block,
         or returns a dynamic value *)
  Definition denote_block (b: block dtyp) (bid_from : block_id) (varargs : option ADDR.addr) : itree (instr_E dvalue) (block_id + dvalue) :=
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
    : (block_id * block_id) -> itree (instr_E dvalue) ((block_id * block_id) + dvalue) :=
    ITree.iter
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

  Definition denote_cfg (f: cfg dtyp) (varargs : option ADDR.addr) : itree (instr_E dvalue) dvalue :=
    r <- denote_ocfg (blks f) varargs (init f,init f) ;;
    match r with
    | inl bid => raise ("Can't find block in denote_cfg " ++ show (snd bid))
    | inr uv  => ret uv
    end.

  (* The denotation of an itree function is a coq function that takes
         a list of uvalues and returns the appropriate semantics. *)
  Definition function_denotation : Type :=
    list dvalue -> itree (L0' dvalue) dvalue.

  Fixpoint combine_lists_varargs {A B:Type} (l1:list A) (l2:list B) : EOB (list (A * B) * list B) :=
    match l1, l2 with
    | [], [] => ret ([], [])
    | x::xs, y::ys =>
        '(l, vargs) <- combine_lists_varargs xs ys ;;
        ret ((x,y)::l, vargs)
    | _, [] =>
        raise_error "combine_lists_varargs: too few arguments"
    | [], vargs =>
        ret ([], vargs)
    end.

  Definition pop_call_frame {E k v exc} `{MemoryE dvalue -< E} `{StackE k v exc -< E} : itree E unit :=
    trigger StackPop;;
    trigger MemPop.

  
  Fixpoint dtyp_of_dvalue (v:dvalue) : EOB dtyp :=
    let list_dtyps :=
      fix go (uvs : list dvalue) : EOB (list dtyp) :=
        match uvs with
        | [] => ret []
        | v::tl =>
            dt <- dtyp_of_dvalue v;;
            dts <- go tl;;
            ret (dt :: dts)
        end
          in
     match v with
           | DVALUE_Addr a => ret DTYPE_Pointer
           | @DVALUE_I sz x => ret (DTYPE_I sz)
           | DVALUE_IPTR x => ret DTYPE_IPTR
           | DVALUE_Double x => ret (DTYPE_FP FP_double)
           | DVALUE_Float x => ret (DTYPE_FP FP_float)
           | DVALUE_Poison t => ret t
           | DVALUE_None => ret DTYPE_Void
           | DVALUE_Struct fields =>
               dts <- list_dtyps fields;;
               ret (DTYPE_Struct dts)
           | DVALUE_Packed_struct fields =>
               dts <- list_dtyps fields;;
               ret (DTYPE_Packed_struct dts)
           | DVALUE_Array (DTYPE_Array sz t) elts =>
               if @NO_VOID_dec t
               then
                 if forallb (fun e => match dtyp_of_dvalue e with
                                   | raise_ret t' => dtyp_eqb t t'
                                   | _ => false end) elts
                    && N.eqb sz (N.of_nat (length elts))
                 then ret (DTYPE_Array (N.of_nat (length elts)) t)
                 else raise_error "dtyp_of_uvalue_fun: mismatched element type in array"
               else raise_error "dtyp_of_uvalue_fun: void in array type"
           | DVALUE_Vector (DTYPE_Vector sz t) elts =>
               if @NO_VOID_dec t
               then
                 if forallb (fun e => match dtyp_of_dvalue e with
                                   | raise_ret t' => dtyp_eqb t t'
                                   | _ => false end) elts
                    && N.eqb sz (N.of_nat (length elts))
                 then
                   if @vector_dtyp_dec t
                   then ret (DTYPE_Vector (N.of_nat (length elts)) t)
                   else raise_error "dtyp_of_uvalue_fun: invalid element type for vector"
                 else raise_error "dtyp_of_uvalue_fun: mismatched element type in vector"
               else raise_error "dtyp_of_uvalue_fun: void in vector type"
                        
    | _ => raise_error "dtyp_of_uvalue_fun: missing case"
           end.


  (* Push call frame, return varargs address *)
  Definition push_call_frame (df:definition dtyp (cfg dtyp)) (args : list dvalue) : itree (L0' dvalue) ADDR.addr :=
    (* We match the arguments variables to the inputs *)
    '(bs, vs) <- lift (combine_lists_varargs (df_args df) args) ;;
    dts <- lift (map_monad dtyp_of_dvalue vs);;
    let dt := DTYPE_Packed_struct dts in
    (* generate the corresponding writes to the local stack frame *)
    trigger (@MemPush dvalue) ;;
    trigger (StackPush bs) ;;
    varargs <- trigger (Alloca dt 1 None);;
    trigger (Store dt varargs (DVALUE_Packed_struct vs));;
    match varargs with
    | DVALUE_Addr varg =>
        ret varg
    | _ => raise "Non-address returned from alloca of varargs"
    end.

  Definition denote_function (df:definition dtyp (cfg dtyp)) : function_denotation :=
    fun (args : list dvalue) =>
      varg <- push_call_frame df args;;
      rv <- translate (@instr_to_L0' dvalue) (denote_cfg (df_instrs df) (Some varg));;
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
    (fundefs : IntMap function_denotation) (dt : dtyp)
    (f_value : dvalue) (args : list dvalue) : itree (L0 dvalue) dvalue :=
    @mrec (@CallE dvalue) (ExternalCallE dvalue +' _)
      (fun T call =>
         match call with
         | Call dt fv args =>
             match lookup_defn fv fundefs with
             | Some f_den => (* If the call is internal *)
                 f_den args
             (* unEitherT (catch_llvm_exc_L0' (f_den args)) *)
             | None =>
                 trigger (ExternalCall dt fv args)
             end
         end) _ (Call dt f_value args).
  
End Denotation.
