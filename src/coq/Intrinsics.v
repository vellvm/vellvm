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
     Util
     LLVMAst
     LLVMEvents
     Error
     IntrinsicsDefinitions.

From ITree Require Import
     ITree.

Import MonadNotation.
Import EqvNotation.
Import ListNotations.


Set Implicit Arguments.
Set Contextual Implicit.

(* (Pure) Intrinsics -------------------------------------------------------- *)

(* The intrinsics interpreter looks for Calls to intrinsics defined by its
   argument and runs their semantic function, raising an error in case of
   exception.  Unknown Calls (either to other intrinsics or external calls) are
   pass through unchanged.
*)
Module Make(A:MemoryAddress.ADDRESS)(LLVMIO: LLVM_INTERACTIONS(A)).

  Module IS := IntrinsicsDefinitions.Make(A)(LLVMIO).
  Include IS.
  Import LLVMIO.
  Import DV.


Typeclasses eauto := 4.
  (* Interprets Call events found in the given association list by their
     semantic functions.  

     SAZ: This definition is trickier than one wants it to be because of the 
     dependent pattern matching.  The indices of the IO constructors need to 
     be used to coerce the result back to the general ITree type.

     We solve it by using the "Convoy Pattern" (see Chlipala's CPDT).  

     callE ~> LLVME 
   *)
Print Instances MonadExc.
  Definition handle_intrinsics (intrinsic_defs : intrinsic_definitions)
    : (ExternalCallE +' IO +' failureE +' debugE) ~> itree (ExternalCallE +' IO +' failureE +' debugE) :=
    (* This is a bit hacky: declarations without global names are ignored by mapping them to empty string *)
    let defs_assoc := List.map (fun '(a,b) =>
                                  match dc_name a with
                                  | Name s => (s,b)
                                  | _ => ("",b)
                                  end
                               ) intrinsic_defs in
    fun X (e : (ExternalCallE +' IO +' failureE +' debugE) X) =>
      match e return itree (ExternalCallE +' IO +' failureE +' debugE) X with
      | inl1 e' =>
        let '(ExternalCall _ fid args) := e' in
        match e' in ExternalCallE Y return X = Y -> itree (ExternalCallE +' IO +' failureE +' debugE) Y with
        | ExternalCall _ fid args =>
          match fid with
          | Name fname =>
            match assoc Strings.String.string_dec fname defs_assoc with
            | Some f => fun pf => 
                         match f args with
                         | inl msg => @raise string _ (@monad_exc_FailureE1E2 (ExternalCallE +' IO) debugE) _ msg
                         | inr result => Ret result
                         end
            | None => fun pf => (eq_rect X (fun a => itree (ExternalCallE +' IO +' failureE +' debugE) a) (ITree.send e)) dvalue pf
            end
          | _ => raise "Unnamed external call."
          end
        end eq_refl
      | inr1 _ => ITree.send e
      end.
        
  Definition evaluate_intrinsics (intrinsic_def : intrinsic_definitions)
             : forall R, itree (ExternalCallE +' IO +' failureE +' debugE) R -> itree (ExternalCallE +' IO +' failureE +' debugE) R  :=
    interp (handle_intrinsics intrinsic_def).

  Definition evaluate_with_defined_intrinsics := evaluate_intrinsics defined_intrinsics.
  
End Make.