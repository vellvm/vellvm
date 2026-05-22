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
  
  Definition handle_memory {E} (h : memM ~> itree E) : MemoryE ~> itree E.
    Set Printing Implicit.
    refine (fun T e => h _ _).
    refine (@handle_memoryM Pa (@MemoryModelPrimitivesV Pa) T _).
    refine (fun T e => h _ (handle_memoryM e)).
    fun T m =>
      match m with
      | MemPush => mempush
      | MemPop => mempop
      | Alloca t n align =>
          addr <- allocate_dtyp t n;;
          ret (DVALUE_Addr addr)
      | Load t a =>
          match a with
          | DVALUE_Addr a =>
              read_dvalue t a
          | _ => mub "Loading from something that isn't an address."
          end
      | Store t a v =>
          match a with
          | DVALUE_Addr a =>
              write_dvalue t a v
          | _ => mub "Writing something to somewhere that isn't an address."
          end
      end.

 
End withParams.

