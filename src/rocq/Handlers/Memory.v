(* begin hide *)
From Stdlib Require Import
  String
  Morphisms.

From ExtLib Require Import
  Structures.Maps
  Data.Map.FMapAList.

From ITree Require Import
  ITree
  Eq.Eqit
  Events.State
  Events.StateFacts
  Basics.MonadState.

From Vellvm Require Import
  Utilities
  Syntax
  Params
  Semantics.LLVMEvents
  Semantics.DynamicValues
  Semantics.Memory.

From QuickChick Require Import Show.


Section withParams.
  Context {Pa : Params}.

  Existing Instance MemoryModelPrimitivesV.
  
  Definition handle_memory {E} (h : memM ~> itree E) : MemoryE ~> itree E :=
    fun T e => h _ (handle_memoryM e).

  (* Hmmm may have made a mistake somewhere: how do I access the current state?
     It is stored in the event, but not at the top level... *)
  Fixpoint memM_interp {E}
    `{FailureE -< E}
    `{UBE -< E}
    `{OOME -< E}
    : memM ~> itree E.
    refine (fun T m => match m with
                    | Mret x => ret x
                    | Moom s => raiseOOM s
                    | Mub s => raiseUB s
                    | Merr s => raise s
                    | Mfresh_addr σ k => _
                    | Mfresh_prov σ k => _
                    end
           ).
      
  Definition mem_state_fresh_provenance (ms : state) : (Provenance * state) :=
    match ms with
    | mkMemState mem_stack pr =>
        let pr' := next_provenance pr in
        (pr', mkMemState mem_stack pr')
    end.


  Definition memM_model {E} : memM ~> itree E.
    intros T e.
    induction e.
  
End withParams.




