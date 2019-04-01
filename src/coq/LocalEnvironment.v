From Coq Require Import
     List
     String.

From ExtLib Require Import
     Programming.Show
     Structures.Monads
     Structures.Maps.

From ITree Require Import 
     ITree
     Effects.Exception
     Effects.State.

From Vellvm Require Import
     LLVMAst
     MemoryAddress
     DynamicValues
     Error.

Set Implicit Arguments.
Set Contextual Implicit.

Import ListNotations.
Import MonadNotation.

Import ITree.Basics.Basics.Monads.

Module LLVM_LOCALS(ADDR:Vellvm.MemoryAddress.ADDRESS).

Module DV := DynamicValues.DVALUE(ADDR).
Export DV.

(* Interactions with local variables for the LLVM IR *)
(* YZ TODO: Change names to better ones ? *)
(* Note: maybe we can spare useless LocalPush for tailcalls *)
Variant Locals : Type -> Type :=
| LocalPush: Locals unit (* Push a fresh environment. *)
| LocalPop : Locals unit (* Pops it back during a ret *)
| LocalWrite (id: raw_id) (dv: dvalue): Locals unit
| LocalRead  (id: raw_id): Locals dvalue.


Section StackMap.
  Context {map : Type}.
  Context {M: Map raw_id dvalue map}.
  Definition stack := list map.
  
  Definition handle_locals {E} `{MonadExc string (itree E)} : Locals ~> stateT stack (itree E) :=
    fun _ e env =>
      match e with
      | LocalPush => Ret (Maps.empty :: env, tt)
      | LocalPop =>
        match env with
        (* CB TODO: should this raise an error? *)
        | [] => failwith "Tried to pop too many stacks."
        | (_::env') => Ret (env', tt)
        end
      | LocalWrite id dv =>
        match env with
        (* CB TODO: This might not be an error... Might have to push frame. Initial stack should start with frame. *)
        | [] => failwith ("Trying to write to environment with no stack frames, id: " ++ to_string id)
        | (vs::env') =>
          let vs' := Maps.add id dv vs
          in Ret (vs' :: env', tt)
        end
      | LocalRead id =>
        match env with
        (* CB TODO: This might not be an error... Might have to push frame *)
        | [] => failwith ("Trying to write to blank environment, id: " ++ to_string id)
        | (vs::env') =>
          match Maps.lookup id vs with
          | Some v => Ret (env, v)
          | None => failwith ("Could not look up id " ++ to_string id)
          end
        end
      end.

  Definition start_stack : stack := [Maps.empty].
  
  Definition run_locals {E} `{MonadExc string (itree E)} : itree (Locals +' E) ~> stateT stack (itree E) :=
    interp_state (case_ handle_locals pure_state).
End StackMap.

End LLVM_LOCALS.
