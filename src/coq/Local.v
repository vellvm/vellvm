From Coq Require Import
     List
     String.

From ExtLib Require Import
     Programming.Show
     Structures.Monads
     Structures.Maps.

From ITree Require Import 
     ITree
     Events.State.

From Vellvm Require Import
     LLVMAst
     MemoryAddress
     DynamicValues
     LLVMEvents
     Error.

Set Implicit Arguments.
Set Contextual Implicit.

Import ListNotations.
Import MonadNotation.

Import ITree.Basics.Basics.Monads.

Module LLVM_LOCAL(ADDR:Vellvm.MemoryAddress.ADDRESS)(LLVMEvents:LLVM_INTERACTIONS(ADDR)).

  Module DV := DynamicValues.DVALUE(ADDR).
  Export DV.
  Import LLVMEvents.

  Section StackMap.
    Context {map : Type}.
    Context {M: Map raw_id dvalue map}.
    Definition stack := list map.
    
    Definition handle_local {E} `{FailureE -< E} : LocalE ~> stateT stack (itree E) :=
      fun _ e env =>
        match e with
        | LocalPush => Ret (Maps.empty :: env, tt)
        | LocalPop =>
          match env with
          (* CB TODO: should this raise an error? *)
          | [] => raise "Tried to pop too many stacks."
          | (_::env') => Ret (env', tt)
          end
        | LocalWrite id dv =>
          match env with
          (* CB TODO: This might not be an error... Might have to push frame. Initial stack should start with frame. *)
          | [] => raise ("Trying to write to environment with no stack frames, id: " ++ to_string id)
          | (vs::env') =>
            let vs' := Maps.add id dv vs
            in Ret (vs' :: env', tt)
          end
        | LocalRead id =>
          match env with
          (* CB TODO: This might not be an error... Might have to push frame *)
          | [] => raise ("Trying to write to blank environment, id: " ++ to_string id)
          | (vs::env') =>
            match Maps.lookup id vs with
            | Some v => Ret (env, v)
            | None => raise ("Could not look up id " ++ to_string id)
            end
          end
        end.

    Definition start_stack : stack := [Maps.empty].
    
    Definition run_local {E} `{FailureE -< E} : LLVM _MCFG ~> stateT stack (LLVM _MCFG1) :=
      interp_state (case_ handle_local pure_state).

  End StackMap.

End LLVM_LOCAL.
