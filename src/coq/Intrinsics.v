(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2018 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)


From Coq Require Import
     ZArith List String.

From ExtLib Require Import
     Structures.Monads
     Programming.Eqv
     Data.String.

From Vellvm Require Import 
     LLVMAst
     Util
     StepSemantics 
     LLVMIO
     Error
     Coqlib
     Numeric.Integers
     Numeric.Floats.


From ITree Require Import
     ITree
     StdEffects.

Import MonadNotation.
Import EqvNotation.
Import ListNotations.


Set Implicit Arguments.
Set Contextual Implicit.

(* (Pure) Intrinsics -------------------------------------------------------- *)

(* This functor module provides a way to (extensibly) add the semantic behavior
   for intrinsics defined outside of the core Vellvm operational semantics.  

   Internally, invocation of an intrinsic looks no different than that of an 
   external function call, so each LLVM intrinsic instruction should produce 
   a Call effect.

   Each intrinsic is identified by its name (a string) and its denotation is 
   given by a function from a list of dynamic values to a dynamic value (or 
   possibly an error).  

   - each intrinsic should "morally" be a total function: assuming the LLVM program 
     is well formed, the intrisnic should always produce an LLVM value (which itself 
     might be poison or undef)

   - error should be returned only in the case that the LLVM program is ill-formed 
     (e.g. if the wrong number and/or type of arguments to the intrinsic is incorrect)

   The interpreter looks for Calls to intrinsics defined by its argument and 
   runs their semantic function, raising an error in case of exception.  Unknown
   Calls (either to other intrinsics or external calls) are pass through unchanged.

   NOTE: The intrinsics that can be defined at this layer of the semantics cannot 
   affect the core interpreter state or the memory model.  This layer is useful
   for implementing intrinsics like floating point operations, etc.
*)


Module Make(A:MemoryAddress.ADDRESS)(LLVMIO: LLVM_INTERACTIONS(A)).
  Import LLVMIO.
  Import DV.

  (* Each (pure) intrinsic is defined by a function of the following type. *)
  Definition semantic_function := (list dvalue) -> err dvalue.

  (* An association list mapping intrinsic names to their semantic definitions *)
  Definition intrinsic_definitions := list (string * semantic_function).

  (* SAZ: This definition is trickier than one wants it to be because of the 
     dependent pattern matching.  The indices of the IO constructors need to 
     be used to coerce the result back to the general ITree type.

     We solve it by using the "Convoy Pattern" (see Chlipala's CPDT).  
   *)
  Definition handle_intrinsics (intrinsic_defs : intrinsic_definitions)
    : eff_hom (IO +' failureE) (IO +' failureE) :=
    fun X (e : (IO +' failureE) X) =>
      match e return itree (IO +' failureE) X with
      | inlE e' =>
        match e' in IO Y return X = Y -> itree (IO +' failureE) Y with
        | Call _ fname args => 
          match assoc Strings.String.string_dec fname intrinsic_defs with
          | Some f => fun pf => 
            match f args with
            | inl msg => fail msg
            | inr result => fail "foo"
            end
          | None => fun pf => (eq_rect X (fun a => itree (IO +' failureE) a) (Vis e (fun x => Ret x))) dvalue pf
          end
        | Store _ _ => fun pf  => (eq_rect X (fun a => itree (IO +' failureE) a) (ITree.liftE e)) unit pf
        | _ => fun pf  => (eq_rect X (fun a => itree (IO +' failureE) a) (ITree.liftE e)) dvalue pf
        end eq_refl
      | inrE _ => ITree.liftE e
      end.
        
  Definition evaluate_intrinsics (intrinsic_def : intrinsic_definitions)
             : forall R, Trace R -> Trace R  :=
    interp (handle_intrinsics intrinsic_def).

End Make.

