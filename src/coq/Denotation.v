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
     ZArith List String 
     FSets.FMapWeakList.

Require Import Integers Floats.

From ExtLib Require Import
     Programming.Show
     Structures.Monads
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
     MemoryAddress
     LLVMEvents
     TypeUtil.

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


     (itree (CallE +' Locals +' ExternalCallE +' IO +' failureE +' debugE)).

     Pure intrinsics, like math. Sin / cos and stuff. Some need to be
     handled at the memory model level, like memcpy.

     Do we need to separate ExternalCalls? Or Memory model
     takes... ExternalCallE +' IO and produces ExternalCallE
     itrees. Handles some ExternalCalls, but not necessarily all of
     them.

     Rename IO to MemE or something.

     (itree (CallE +' Locals +' ExternalCallE +' IO +' failureE +' debugE)).

     - Denotation: gets rid of CallE denote_mcfg (denote_cfg in practice never emits ExternalCalls)
       + Linking, do we want to make this distinction?
     - LocalEnvironment: gets rid of locals
     - Intrinsics.v: should this be two?
     - Memory.v: takes ExternalCallE and IO


     - Add MemoryIntrinsic to IO, kind of like how Call used to be. Can now interpret away entirely inside memory model
       + Call would have to figure out which ones are memory
         intrinsics and which ones are not. Should have this information
         while linking CFGs.
       + General memory models need a way of registering which intrinsics they handle.
  *)

  (*
  (* CB TODO: Can we have 1 instance of MonadExc? *)
  CoFixpoint catch_LLVM1 {E F X} `{E -< F} `{failureE -< F}
             (f:string -> LLVM1 X)
             (t : LLVM1 X) : LLVM1 X :=
    match (observe t) with
    | RetF x => Ret x
    | TauF t => Tau (catch_LLVM1 f t)
    | VisF _ (inr1 (inr1 (inr1 (inr1 (inl1 (Throw s)))))) k => f s
    | VisF _ e k => vis e (fun x => catch_LLVM1 f (k x))
    end.
   *)
(*
  Global Instance monad_exc_LLVM1 : (MonadExc string LLVM1) :=
    {
      raise := raise_FailureE ;
      catch := fun T m f => catch_LLVM1 f m ;
    }.
 *)


  (* The mutually recursive functions are tied together, interpreting away all internal calls*)
 
  (* Environments ------------------------------------------------------------- *)
  (* Used to implement (static) global environments.
     The same data-structure will be reused for local (dynamic) environments.
   *)
  Module ENV := FMapWeakList.Make(AstLib.RawIDOrd).

  (* Global environments *)
  Definition genv := ENV.t dvalue.

  Definition lookup_env {X} (e:ENV.t X) (id:raw_id) : err X :=
    match ENV.find id e with
    | Some v => ret v
    | None => failwith ("lookup_env: failed to find id " ++ (to_string id))
    end.

  (* Lookup function for identifiers.
     Returns directly the dynamic value if the identifier is global,
     otherwise emits the corresponding read event.
   *)
  (* YZ note: read/writes for local and load/store for memory is fine? *)
  Definition lookup_id (g:genv) (i:ident) : LLVM_CFG dvalue :=
    match i with
    | ID_Global x => lift_err ret (lookup_env g x)
    | ID_Local x  =>  (trigger (LocalRead x))
    end.

  (* Lookup attempting to cast adresses into function identifiers *)
  Definition reverse_lookup_function_id (g:genv) (a:A.addr) : err raw_id :=
    let f x :=
        match x with
        | (_, DVALUE_Addr b) => if a ~=? b then true else false
        | _ => false
        end
    in
    match List.find f (ENV.elements g) with
    | None => failwith "reverse_lookup_function_id failed"
    | Some (fid, _) => ret fid
    end.

  Section CONVERSIONS.
    (* Conversions can't go into DynamicValues because Int2Ptr and Ptr2Int casts 
       generate memory effects. *)
    Definition eval_conv_h conv t1 x t2 : LLVM_CFG dvalue :=
      match conv with
      | Trunc =>
        match t1, x, t2 with
        | TYPE_I 8, DVALUE_I8 i1, TYPE_I 1 =>
          ret (DVALUE_I1 (repr (unsigned i1)))
        | TYPE_I 32, DVALUE_I32 i1, TYPE_I 1 =>
          ret (DVALUE_I1 (repr (unsigned i1)))
        | TYPE_I 32, DVALUE_I32 i1, TYPE_I 8 =>
          ret (DVALUE_I8 (repr (unsigned i1)))
        | TYPE_I 64, DVALUE_I64 i1, TYPE_I 1 =>
          ret (DVALUE_I1 (repr (unsigned i1)))
        | TYPE_I 64, DVALUE_I64 i1, TYPE_I 8 =>
          ret (DVALUE_I8 (repr (unsigned i1)))
        | TYPE_I 64, DVALUE_I64 i1, TYPE_I 32 =>
          ret (DVALUE_I32 (repr (unsigned i1)))
        | _, _, _ => raise "ill typed-conv"
        end
      | Zext =>
        match t1, x, t2 with
        | TYPE_I 1, DVALUE_I1 i1, TYPE_I 8 =>
          ret (DVALUE_I8 (repr (unsigned i1)))
        | TYPE_I 1, DVALUE_I1 i1, TYPE_I 32 =>
          ret (DVALUE_I32 (repr (unsigned i1)))
        | TYPE_I 1, DVALUE_I1 i1, TYPE_I 64 =>
          ret (DVALUE_I64 (repr (unsigned i1)))
        | TYPE_I 8, DVALUE_I8 i1, TYPE_I 32 =>
          ret (DVALUE_I32 (repr (unsigned i1)))
        | TYPE_I 8, DVALUE_I8 i1, TYPE_I 64 =>
          ret (DVALUE_I64 (repr (unsigned i1)))
        | TYPE_I 32, DVALUE_I32 i1, TYPE_I 64 =>
          ret (DVALUE_I64 (repr (unsigned i1)))
        | _, _, _ => raise "ill typed-conv"
        end
      | Sext =>
        match t1, x, t2 with
        | TYPE_I 1, DVALUE_I1 i1, TYPE_I 8 =>
          ret (DVALUE_I8 (repr (signed i1)))
        | TYPE_I 1, DVALUE_I1 i1, TYPE_I 32 =>
          ret (DVALUE_I32 (repr (signed i1)))
        | TYPE_I 1, DVALUE_I1 i1, TYPE_I 64 =>
          ret (DVALUE_I64 (repr (signed i1)))
        | TYPE_I 8, DVALUE_I8 i1, TYPE_I 32 =>
          ret (DVALUE_I32 (repr (signed i1)))
        | TYPE_I 8, DVALUE_I8 i1, TYPE_I 64 =>
          ret (DVALUE_I64 (repr (signed i1)))
        | TYPE_I 32, DVALUE_I32 i1, TYPE_I 64 =>
          ret (DVALUE_I64 (repr (signed i1)))
        | _, _, _ => raise "ill typed-conv"
        end
      | Bitcast =>
        match t1, x, t2 with
        | TYPE_I bits1, x, TYPE_I bits2 =>
          if bits1 =? bits2 then ret x else raise "unequal bitsize in cast"
        | TYPE_Pointer t1, DVALUE_Addr a, TYPE_Pointer t2 =>
          ret (DVALUE_Addr a) 
        | _, _, _ => raise "ill-typed_conv"
        end
      | Uitofp =>
        match t1, x, t2 with
        | TYPE_I 1, DVALUE_I1 i1, TYPE_Float =>
          ret (DVALUE_Float (Float32.of_intu (repr (unsigned i1))))

        | TYPE_I 8, DVALUE_I8 i1, TYPE_Float =>
          ret (DVALUE_Float (Float32.of_intu (repr (unsigned i1))))

        | TYPE_I 32, DVALUE_I32 i1, TYPE_Float =>
          ret (DVALUE_Float (Float32.of_intu (repr (unsigned i1))))

        | TYPE_I 64, DVALUE_I64 i1, TYPE_Float =>
          ret (DVALUE_Float (Float32.of_intu (repr (unsigned i1))))

        | TYPE_I 1, DVALUE_I1 i1, TYPE_Double =>
          ret (DVALUE_Double (Float.of_longu (repr (unsigned i1))))

        | TYPE_I 8, DVALUE_I8 i1, TYPE_Double =>
          ret (DVALUE_Double (Float.of_longu (repr (unsigned i1))))

        | TYPE_I 32, DVALUE_I32 i1, TYPE_Double =>
          ret (DVALUE_Double (Float.of_longu (repr (unsigned i1))))
              
        | TYPE_I 64, DVALUE_I64 i1, TYPE_Double =>
          ret (DVALUE_Double (Float.of_longu (repr (unsigned i1))))

        | _, _, _ => raise "ill typed Uitofp"
        end
      | Sitofp =>
        match t1, x, t2 with
        | TYPE_I 1, DVALUE_I1 i1, TYPE_Float =>
          ret (DVALUE_Float (Float32.of_intu (repr (signed i1))))

        | TYPE_I 8, DVALUE_I8 i1, TYPE_Float =>
          ret (DVALUE_Float (Float32.of_intu (repr (signed i1))))

        | TYPE_I 32, DVALUE_I32 i1, TYPE_Float =>
          ret (DVALUE_Float (Float32.of_intu (repr (signed i1))))

        | TYPE_I 64, DVALUE_I64 i1, TYPE_Float =>
          ret (DVALUE_Float (Float32.of_intu (repr (signed i1))))

        | TYPE_I 1, DVALUE_I1 i1, TYPE_Double =>
          ret (DVALUE_Double (Float.of_longu (repr (signed i1))))

        | TYPE_I 8, DVALUE_I8 i1, TYPE_Double =>
          ret (DVALUE_Double (Float.of_longu (repr (signed i1))))

        | TYPE_I 32, DVALUE_I32 i1, TYPE_Double =>
          ret (DVALUE_Double (Float.of_longu (repr (signed i1))))
              
        | TYPE_I 64, DVALUE_I64 i1, TYPE_Double =>
          ret (DVALUE_Double (Float.of_longu (repr (signed i1))))

        | _, _, _ => raise "ill typed Sitofp"
        end 
      | Fptoui
      | Fptosi 
      | Fptrunc
      | Fpext => raise "TODO: unimplemented numeric conversion"
      | Inttoptr =>
        match t1, t2 with
        | TYPE_I 64, TYPE_Pointer t => vis (ItoP x) ret
        | _, _ => raise "ERROR: Inttoptr got illegal arguments"
        end 
      | Ptrtoint =>
        match t1, t2 with
        | TYPE_Pointer t, TYPE_I 64 => vis (PtoI x) ret
        | _, _ => raise "ERROR: Ptrtoint got illegal arguments"
        end
      end.
    Arguments eval_conv_h _ _ _ _ : simpl nomatch.

    Definition eval_conv conv t1 x t2 : LLVM_CFG dvalue :=
      match t1, x with
      | TYPE_I bits, dv =>
        eval_conv_h conv t1 dv t2
      | TYPE_Vector s t, (DVALUE_Vector elts) =>
        (* In the future, implement bitcast and etc with vectors *)
        raise "vectors unimplemented"
      | _, _ => eval_conv_h conv t1 x t2
      end.
    Arguments eval_conv _ _ _ _ : simpl nomatch.

  End CONVERSIONS.

  Definition dv_zero_initializer (t:dtyp) : err dvalue :=
    failwith "dv_zero_initializer unimplemented".

  Section IN_CFG_CONTEXT.

    (* YZ TODO : [eval_typ] is the only bit that still rely on the ambient mcfg.
       That probably should not be the case.
     *)
    Variable CFG:mcfg.

    Definition eval_typ (t:typ) : dtyp :=
      TypeUtil.normalize_type_dtyp (m_type_defs CFG) t.

    Section IN_GLOBAL_ENVIRONMENT.

      (* Global environments are set at the top-level, and static *)
      Variable g : genv.

(*
  [denote_exp] is the main entry point for evaluating LLVM expressions.
  top : is the type at which the expression should be evaluated (if any)
  INVARIANT: 
    - top may be None only for 
        - EXP_Ident 
        - OP_* cases

    - top must be Some t for the remaining EXP_* cases
      Note that when top is Some t, the resulting dvalue can never be
      a function pointer for a well-typed LLVM program.

  Expressions are denoted as itrees that return a [dvalue].
 *)

      Fixpoint denote_exp (top:option dtyp) (o:exp) {struct o} : LLVM_CFG dvalue :=
        let eval_texp '(t,ex) :=
            let dt := eval_typ t in
            v <- denote_exp (Some dt) ex ;;
            ret v
        in
        match o with
        | EXP_Ident i =>
          lookup_id g i

        | EXP_Integer x =>
          match top with
          | None                => raise "denote_exp given untyped EXP_Integer"
          | Some (DTYPE_I bits) => lift_err ret (coerce_integer_to_int bits x)
          | _                   => raise "bad type for constant int"
          end

        | EXP_Float x =>
          match top with
          | None              => raise "denote_exp given untyped EXP_Float"
          | Some DTYPE_Float  => ret (DVALUE_Float (Float32.of_double x))
          | Some DTYPE_Double => ret (DVALUE_Double x)
          | _                 => raise "bad type for constant float"
          end

        | EXP_Hex x =>
          match top with
          | None              => raise "denote_exp given untyped EXP_Hex"
          | Some DTYPE_Float  => ret (DVALUE_Float (Float32.of_double x))
          | Some DTYPE_Double => ret (DVALUE_Double x)
          | _                 => raise "bad type for constant hex float"
          end

        | EXP_Bool b =>
          match b with
          | true  => ret (DVALUE_I1 one)
          | false => ret (DVALUE_I1 zero)
          end

        | EXP_Null => ret (DVALUE_Addr A.null)

        | EXP_Zero_initializer =>
          match top with
          | None   => raise "denote_exp given untyped EXP_Zero_initializer"
          | Some t => lift_err ret (dv_zero_initializer t)
          end

        | EXP_Cstring s => raise "EXP_Cstring not yet implemented"

        | EXP_Undef =>
          match top with
          | None   => raise "denote_exp given untyped EXP_Undef"
          | Some t => ret DVALUE_Undef  (* TODO: use t for size? *)
          end

        (* Question: should we do any typechecking for aggregate types here? *)
        (* Option 1: do no typechecking: *)
        | EXP_Struct es =>
          vs <- map_monad eval_texp es ;;
          ret (DVALUE_Struct vs)

        (* Option 2: do a little bit of typechecking *)
        | EXP_Packed_struct es =>
          match top with
          | None => raise "denote_exp given untyped EXP_Struct"
          | Some (DTYPE_Packed_struct _) =>
            vs <- map_monad eval_texp es ;;
            ret (DVALUE_Packed_struct vs)
          | _ => raise "bad type for VALUE_Packed_struct"
          end

        | EXP_Array es =>
          vs <- map_monad eval_texp es ;;
          ret (DVALUE_Array vs)
             
        | EXP_Vector es =>
          vs <- map_monad eval_texp es ;;
          ret (DVALUE_Vector vs)

        | OP_IBinop iop t op1 op2 =>
          let dt := eval_typ t in
          v1 <- denote_exp (Some dt) op1 ;;
          v2 <- denote_exp (Some dt) op2 ;;
          lift_err ret (eval_iop iop v1 v2)

        | OP_ICmp cmp t op1 op2 =>
          let dt := eval_typ t in
          v1 <- denote_exp (Some dt) op1 ;;
          v2 <- denote_exp (Some dt) op2 ;;
          lift_err ret (eval_icmp cmp v1 v2)

        | OP_FBinop fop fm t op1 op2 =>
          let dt := eval_typ t in    
          v1 <- denote_exp (Some dt) op1 ;;
          v2 <- denote_exp (Some dt) op2 ;;
          lift_err ret (eval_fop fop v1 v2)

        | OP_FCmp fcmp t op1 op2 =>
          let dt := eval_typ t in
          v1 <- denote_exp (Some dt) op1 ;;
          v2 <- denote_exp (Some dt) op2 ;;
          lift_err ret (eval_fcmp fcmp v1 v2)
             
        | OP_Conversion conv t1 op t2 =>
          let dt1 := eval_typ t1 in
          v <- denote_exp (Some dt1) op ;;
          eval_conv conv t1 v t2
            
        | OP_GetElementPtr _ (TYPE_Pointer t, ptrval) idxs =>
          let dt := eval_typ t in
          vptr <- denote_exp (Some DTYPE_Pointer) ptrval ;;
          vs <- map_monad (fun '(_, index) => denote_exp (Some (DTYPE_I 32)) index) idxs ;;
          trigger (GEP dt vptr vs)

        | OP_GetElementPtr _ (_, _) _ =>
          raise "getelementptr has non-pointer type annotation"
                
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

        | OP_ExtractValue strop idxs =>
          let '(t, str) := strop in
          let dt := eval_typ t in
          str <- denote_exp (Some dt) str;;
          let fix loop str idxs : err dvalue :=
              match idxs with
              | [] => ret str
              | i :: tl =>
                v <- index_into_str str i ;;
               loop v tl
              end in
          lift_err ret (loop str idxs)
                   
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
                
        | OP_Select (t, cnd) (t1, op1) (t2, op2) =>
          let dt  := eval_typ t in
          let dt1 := eval_typ t1 in
          let dt2 := eval_typ t2 in
          cndv <- denote_exp (Some dt) cnd ;;
          v1   <- denote_exp (Some dt1) op1 ;;
          v2   <- denote_exp (Some dt2) op2 ;;
          lift_err ret (eval_select cndv v1 v2)

        end.

      Arguments denote_exp _ : simpl nomatch.

      Definition eval_op (o:exp) : LLVM_CFG dvalue :=
        denote_exp None o.
      Arguments eval_op _ : simpl nomatch.

      (* An instruction has only side-effects, it therefore returns [unit] *)
      Definition denote_instr (i: (instr_id * instr)): LLVM_CFG unit :=
        match i with
        (* Pure operations *)
        | (IId id, INSTR_Op op) =>
          dv <- eval_op op ;;
          trigger (LocalWrite id dv)

        (* Allocation *)
        | (IId id, INSTR_Alloca t _ _) =>
          dv <- trigger (Alloca (eval_typ t));;
          trigger (LocalWrite id dv)

        (* Load *)
        | (IId id, INSTR_Load _ t (u,ptr) _) =>
          da <- denote_exp (Some (eval_typ u)) ptr ;;
          dv <- trigger (Load (eval_typ t) da);;
          trigger (LocalWrite id dv)

        (* Store *)
        | (IVoid _, INSTR_Store _ (t, val) (u, ptr) _) =>
          da <- denote_exp (Some (eval_typ t)) val ;;
          dv <- denote_exp (Some (eval_typ u)) ptr ;;
          trigger (Store da dv)
        | (_, INSTR_Store _ _ _ _) => raise "ERROR: Store to non-void ID"

        (* Call *)
        | (pt, INSTR_Call (t, f) args) =>
          debug ("call") ;;
          fv  <- denote_exp None f ;; 
          dvs <-  map_monad (fun '(t, op) => (denote_exp (Some (eval_typ t)) op)) args ;; 
          (* Checks whether [fv] a function pointer *)
           match fv with
           | DVALUE_Addr addr =>
             (* TODO: lookup fid given addr from global environment *)
             fid <- lift_err ret (reverse_lookup_function_id g addr) ;;
             (* YZ TODO: MARKER1 Shouldn' we raise an error here if fid is not a Name? *)
             debug ("  fid:" ++ to_string fid) ;;
             (* trigger (LocalPush);; *) (* We push a fresh environment on the stack. TODO: Actually done in denote_mcfg, to remove after confirmation *) 
             dv <- trigger (Call (eval_typ t) fid dvs);;
             match pt with
             | IVoid _ => ret tt
             | IId id  => trigger (LocalWrite id dv)
             end      
           | _ => raise "call got non-function pointer"
           end

        | (_, INSTR_Comment _) => ret tt

        | (_, INSTR_Unreachable) => raise "IMPOSSIBLE: unreachable in reachable position" 

        (* Currently unhandled LLVM instructions *)
        | (_, INSTR_Fence)
        | (_, INSTR_AtomicCmpXchg) 
        | (_, INSTR_AtomicRMW)
        | (_, INSTR_VAArg)
        | (_, INSTR_LandingPad) => raise "Unsupported LLVM instruction"

        (* Error states *)                                     
        | (_, _) => raise "ID / Instr mismatch void/non-void"
                         
        end.

      (* A [terminator] either returns from a function call, producing a [dvalue],
         or jumps to a new [block_id]. *)
      Definition denote_terminator (t: terminator): LLVM_CFG (block_id + dvalue) :=
        match t with

        | TERM_Ret (t, op) =>
          dv <- denote_exp (Some (eval_typ t)) op ;;
             (* YZ : Hesitant between three options.
                1. emit the pop events here and return the dvalue (current choice);
                2. introduce a Return event that would be handled at the same time as Call and do it;
                3. mix of both: can return the dynamic value and have no Ret event, but pop in denote_mcfg
              *)
          (* trigger LocalPop;;  *) (* TODO: actually done in denote_mcfg. Remove after validation *)
          ret (inr dv)

        | TERM_Ret_void =>
          (* trigger LocalPop;;  *) (* TODO: actually done in denote_mcfg. Remove after validation *)
          ret (inr DVALUE_None)

        | TERM_Br (t,op) br1 br2 =>
          dv <- denote_exp (Some (eval_typ t)) op ;; 
          match dv with 
          | DVALUE_I1 comparison_bit =>
            if eq comparison_bit one then
              ret (inl br1)
            else
              ret (inl br2)
          | _ => raise "Br got non-bool value"
          end 

        | TERM_Br_1 br => ret (inl br) 

        (* Currently unhandled LLVM terminators *)                                  
        | TERM_Switch _ _ _
        | TERM_IndirectBr _ _
        | TERM_Resume _
        | TERM_Invoke _ _ _ _ => raise "Unsupport LLVM terminator" 
        end.

      (* Denoting a list of instruction simply binds the trees together *)
      Fixpoint denote_code (c: code): LLVM_CFG unit :=
        match c with
        | nil => ret tt
        | i::c => denote_instr i;; denote_code c
        end.

      (* A block ends with a terminator, it either jumps to another block,
         or returns a dynamic value *)
      Definition denote_block (b: block) : LLVM_CFG (block_id + dvalue) :=
        denote_code b.(blk_code);;
        denote_terminator (snd b.(blk_term)).

      (* YZ FIX: no need to push/pop, but do all the assignments afterward *)
      (* One needs to be careful when denoting phi-nodes: they all must
         be evaluated in the same environment.
         We therefore starts the denotation of a phi-node by pushing a
         local copy of the environment of the stack, that we pop back
         once we are finished evaluating the expression.
         We then bind the resulting value in the underlying environment.
       *)
      Definition denote_phi (bid : block_id) (id_p : local_id * phi) : LLVM_CFG (local_id * dvalue) :=
        let '(id, Phi t args) := id_p in
        match assoc RawIDOrd.eq_dec bid args with
        | Some op =>
          let dt := eval_typ t in
          dv <- denote_exp (Some dt) op ;;
          ret (id,dv)
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
      (* YZ Note: This should be sufficient to denote LLVM programs.
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
      Definition denote_cfg (f: cfg) : LLVM_CFG dvalue :=
        loop (fun (bid : block_id + block_id) =>
                match bid with
                | inl bid
                | inr bid =>
                  match find_block f.(blks) bid with
                  | None => raise ("Can't find block in denote_cfg " ++ to_string bid)
                  | Some block =>
                    (* We denote the block *)
                    bd <- denote_block block;;
                    (* And set the phi-nodes of the new destination, if any *)
                    match bd with
                    | inr dv => ret (inr dv)
                    | inl bid =>
                      dvs <- map_monad (denote_phi bid) block.(blk_phis) ;; (* mapM_ :(? *)
                      map_monad (fun '(id,dv) => trigger (LocalWrite id dv)) dvs;;
                      ret (inl bid)
                    end
                  end
                end
             ) f.(init).

      (* TODO : Move this somewhere else *)
      Fixpoint combine_lists_err {A B:Type} (l1:list A) (l2:list B) : err (list (A * B)) :=
        match l1, l2 with
        | [], [] => ret []
        | x::xs, y::ys =>
          l <- combine_lists_err xs ys ;;
            ret ((x,y)::l)
        | _, _ => failwith "combine_lists_err: different length lists"
        end.

      (* We now turn to the second knot to be tied: a top-level LLVM program is a set
         of mutually recursively defined functions, i.e. [cfg]s. We hence need to
         resolve this mutually recursive definition by interpreting away the call events.
         As mentionned above, calls are not tail recursive: we need a more general fixpoint
         operator than [loop], which [mrec] provides.
       *)
      (* A slight complication comes from the fact that not all call events will be interpreted
         away as such. Some of them correspond to external calls -- to intrinsics -- that will
         be kept uninterpreted for now.
         Since the type of [mrec] forces us to get rid of the [CallE] family of events that we
         interpret, we therefore cast external calls into an isomorphic family of events
         [ExternalCallE].
       *)
      (* YZ Note: we could have chosen to distinguish both kinds of calls in [denote_instr] *)
      Definition denote_mcfg : dtyp -> function_id -> list dvalue -> LLVM_MCFG dvalue :=
        fun dt f_name args =>
          @mrec CallE _
                (fun T call =>
                   match call with
                   | Call dt f_name args =>
                     match (find_function CFG f_name) with
                     | Some fndef => (* If the call is internal *)
                       let (_, ids, cfg) := fndef in
                       (* We match the arguments variables to the inputs; *)
                       bs <- lift_err ret (combine_lists_err ids args) ;;
                       trigger LocalPush ;;  (* YZ Note: Could be done by denote_instr of Call. But then need to be wary of external calls *)
                       (* generate the corresponding writes; *)
                       map_monad (fun '(id, dv) => trigger (LocalWrite id dv)) bs ;;
                       (* and denote the [cfg]. *)
                       res <- denote_cfg cfg;;
                       trigger LocalPop;;  (* YZ Note: Could be done by denote_terminator of Ret. But then need to be wary of external calls *)
                       ret res
                     | None =>
                       (* This must have been a registered external function  *)
                       (* We _don't_ push a LLVM stack frame, since the external *)
                       (* call takes place in one "atomic" step. *)

                       (* We cast the call into ExternalCallE *)
                       (* YZ TODO: cast them into MemoryIntrinsic if applicable *)
                       trigger (Intrinsic dt f_name args)

                       (* CB / YZ TODO: Should we check weither f_name is a [Name] here?
                          Note sure why we only worry about it in the external call case.
                          See also remark MARKER1 *)
                      (* In the old code, we hade:
                      match fid with
                      | Name s => (...)
                      | _ => raise ("step: no function " (* ++ (string_of fid) *))
                      end *)
              end
            end
         ) _ (Call dt f_name args).

    End IN_GLOBAL_ENVIRONMENT.

  End IN_CFG_CONTEXT.

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
Definition init_state (fname:string) : LLVM (failureE +' debugE) state :=
  g <- build_global_environment ;;
  fentry <- trywith ("INIT: no function named " ++ fname) (find_function_entry CFG (Name fname)) ;;
  let 'FunctionEntry ids pc_f := fentry in
    ret (g, pc_f, (@ENV.empty dvalue), []).

CoFixpoint step_sem (r:result) : LLVM (failureE +' debugE) dvalue :=
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

Definition raise_p {X} (p:pc) s : LLVM (failureE +' debugE) X := raise (s ++ " in block: " ++ (to_string p)).
Definition cont (s:state)  : LLVM (failureE +' debugE) result := ret (Step s).
Definition halt (v:dvalue) : LLVM (failureE +' debugE) result := ret (Done v).

 *)
(*
Definition jump (fid:function_id) (bid_src:block_id) (bid_tgt:block_id) (g:genv) (e_init:env) (k:stack) : LLVM (failureE +' debugE) result :=
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
       [| block|]: (block_id * block_id) -> LLVME (block_id * block_id)
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
        (* We _don't_ push a LLVM stack frame, since the external *)
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
