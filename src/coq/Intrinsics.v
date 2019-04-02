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
     LLVMIO
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


  (* Interprets Call events found in the given association list by their
     semantic functions.  

     SAZ: This definition is trickier than one wants it to be because of the 
     dependent pattern matching.  The indices of the IO constructors need to 
     be used to coerce the result back to the general ITree type.

     We solve it by using the "Convoy Pattern" (see Chlipala's CPDT).  
   *)
  Definition handle_intrinsics (intrinsic_defs : intrinsic_definitions)
    : (IO +' (failureE +' debugE)) ~> LLVM (failureE +' debugE) :=
    (* This is a bit hacky: declarations without global names are ignored by mapping them to empty string *)
    let defs_assoc := List.map (fun '(a,b) =>
                                  match dc_name a with
                                  | Name s => (s,b)
                                  | _ => ("",b)
                                  end
                               ) intrinsic_defs in
    fun X (e : (IO +' (failureE +' debugE)) X) =>
      match e return LLVM (failureE +' debugE) X with
      | inl1 e' =>
        match e' in IO Y return X = Y -> LLVM (failureE +' debugE) Y with
        | Call _ fname args => 
          match assoc Strings.String.string_dec fname defs_assoc with
          | Some f => fun pf => 
            match f args with
            | inl msg => raise msg
            | inr result => Ret result
            end
          | None => fun pf => (eq_rect X (fun a => LLVM (failureE +' debugE) a) (ITree.trigger e)) dvalue pf
          end
        | Store _ _ => fun pf  => (eq_rect X (fun a => LLVM (failureE +' debugE) a) (ITree.trigger e)) unit pf
        | _ => fun pf  => (eq_rect X (fun a => LLVM (failureE +' debugE) a) (ITree.trigger e)) dvalue pf
        end eq_refl
      | inr1 _ => ITree.trigger e
      end.
        
  Definition evaluate_intrinsics (intrinsic_def : intrinsic_definitions)
             : forall R, LLVM (failureE +' debugE) R -> LLVM (failureE +' debugE) R  :=
    interp (handle_intrinsics intrinsic_def).

  Definition evaluate_with_defined_intrinsics := evaluate_intrinsics defined_intrinsics.
  
End Make.