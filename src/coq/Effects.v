(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import ZArith List String Omega.
Require Import  Vellvm.Classes Vellvm.Util.
Require Import paco.
Import ListNotations.
Open Scope positive_scope.

Set Implicit Arguments.
Set Contextual Implicit.

Module Type EffT.
  (* The effects interface is parameterized by the language's types and the 
   memory model's notion of addresses. *)
  Parameter typ : Set.
  Parameter addr : Set.
End EffT.

Module Effects(ET:EffT).
Export ET.
  
(* TODO: Add other memory effects, such as synchronization operations *)
(* Notes: 
   - To allow the memory model to correctly model stack alloca deallocation,
     we would also have to expose the "Ret" instruction. 

   - What is the correct way to model global data? 
*)
Inductive effects (dvalue:Type) (d:Type) : Type :=
| Alloca (t:typ)  (k:dvalue -> d)        (* Stack allocation *)
| Load   (a:addr) (k:dvalue -> d)
| Store  (a:addr) (v:dvalue) (k:d)
| Call   (v:dvalue) (k:dvalue -> d)
.    

Definition effects_map {A B dvalue} (f:A -> B) (m:effects dvalue A) : effects dvalue B :=
  match m with
  | Alloca t g => Alloca t (fun a => f (g a))
  | Load a g  => Load a (fun dv => f (g dv))
  | Store a dv d => Store a dv (f d)
  | Call a d => Call a (fun dv => f (d dv))
  end.

Instance effects_functor (dvalue:Type) : @Functor (effects dvalue) := fun A => fun B => @effects_map A B dvalue.
Program Instance effects_functor_eq_laws (dvalue:Type) : (@FunctorLaws (effects dvalue)) (@effects_functor dvalue) (@eq).
Next Obligation.
  unfold fmap. unfold effects_functor. unfold effects_map. destruct a; reflexivity.
Defined.
Next Obligation.
  unfold fmap. unfold effects_functor. unfold effects_map. destruct a; reflexivity.
Defined.  

(* Domain of semantics *)
CoInductive D dvalue X :=
| Ret : X -> D dvalue X
| Fin : dvalue -> D dvalue X
| Err : string -> D dvalue X 
| Tau : D dvalue X -> D dvalue X
| Eff : effects dvalue (D dvalue X) -> D dvalue X
.

CoFixpoint d_map {A B dvalue} (f:A -> B) (d:D dvalue A) : D dvalue B :=
  match d with
    | Ret a => Ret (f a)
    | Fin d => Fin d
    | Err s => Err s
    | Tau d' => Tau (d_map f d')
    | Eff m => Eff (effects_map (d_map f) m)
  end.

Section UNFOLDING.

Definition id_match_d {A dvalue} (d:D dvalue A) : D dvalue A :=
  match d with
    | Ret a => Ret a
    | Fin d => Fin d
    | Err s => Err s
    | Tau d' => Tau d'
    | Eff m => Eff m
  end.

Lemma id_d_eq : forall A dvalue (d:D dvalue A),
  d = id_match_d d.
Proof.
  destruct d; auto.
Qed.

End UNFOLDING.

Arguments id_d_eq {_ _} _ .


Instance D_functor (dvalue:Type) : @Functor (D dvalue) := fun A => fun B => @d_map A B dvalue.

(* Probably a functor only up to stuttering equivalence. *)
(*
Program Instance D_functor_eq_laws : (@FunctorLaws D) D_functor (@eq).
*)

(* Note: for guardedness, bind Ret introduces extra Tau *)
Definition bind {A B dvalue} (m:D dvalue A) (f:A -> D dvalue B) : D dvalue B :=
  (cofix bindf m:= 
     match m with
       | Ret a => Tau (f a)
       | Fin d => Fin d
       | Err s => Err s
       | Tau d' => Tau (bindf d')
       | Eff m => Eff (effects_map bindf m)
     end) m.

Program Instance D_monad (dvalue:Type) : (@Monad (D dvalue)) (@D_functor dvalue) := _.
Next Obligation.
  split.
  - intros. apply Ret. exact X.
  - intros A B. apply bind.
Defined.
  
Inductive Empty :=.

End Effects.