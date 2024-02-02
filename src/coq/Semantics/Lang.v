From Vellvm Require Import
     Semantics.Memory.MemBytes
     Semantics.LLVMParams
     Semantics.MemoryParams
     Semantics.GepM
     Semantics.Denotation
     Semantics.ConcretizationParams
     
     Handlers.Global
     Handlers.Stack
     Handlers.Intrinsics
     Handlers.Pick
     Handlers.MemoryModel
     Handlers.MemoryInterpreters
     Handlers.Concretization.


  Module Type Memory (MP: PARAMS) (MMSP : MemoryModelSpecPrimitives MP) <: MMC MP.
    Include  MMSP.
    Module MPS := (_ADD_SERIALIZE MP).
    Include MPS.
    Include (MemoryModelSpec MP).
    Include (MemoryExecMonad MP).
    Include (MemoryModelExecPrimitives MP).
    Include (MemoryModelExec MP).
    Include (Concretization.Make MP).

    Module MEM_SPEC_INTERP := MakeMemorySpecInterpreter MP.
    Module MEM_EXEC_INTERP := MakeMemoryExecInterpreter MP.

    (* Concretization *)
    Export MP.IP MP.ByteImpl MP.GEP.
  End Memory.


  (* SAZ This is actually not needed, should be MMIC over in MemoryModelImplemention.v *)
  Module Type MemoryBig (MP: PARAMS_BIG) (MMSP : MemoryModelSpecPrimitives MP) <: MMC MP.
    Include  MMSP.
    Module MPS := (_ADD_SERIALIZE MP).
    Include MPS.
    Include (MemoryModelSpec MP).
    Include (MemoryExecMonad MP).
    Include (MemoryModelExecPrimitives MP).
    Include (MemoryModelExec MP).
    Include (Concretization.Make MP).
    
    Module MEM_SPEC_INTERP := MakeMemorySpecInterpreter MP.
    Module MEM_EXEC_INTERP := MakeMemoryExecInterpreter MP.
    
    (* Concretization *)
    Export MP.IP MP.ByteImpl MP.GEP.
  End MemoryBig.


  Module Type LANG (MP : PARAMS) (M : MemoryModelSpecPrimitives MP).
    Include MP.
    
    (* Handlers *)
    Module Global     := Global.Make MP.
    Module Local      := Local.Make MP.
    Module Stack      := Stack.Make MP.
    Module Intrinsics := Intrinsics.Make MP.
  End LANG.
    

  Module Lang (MP: PARAMS) (M : MemoryModelSpecPrimitives MP) <: LANG MP M.
    Include MP.
    
    (* Handlers *)
    Module Global     := Global.Make MP.
    Module Local      := Local.Make MP.
    Module Stack      := Stack.Make MP.
    Module Intrinsics := Intrinsics.Make MP.
    (* Memory *)
    Include Memory MP M.

    (* Pick handler (depends on memory / concretization) *)
    Include Pick.Make MP.

    (* Denotation *)
    Include Denotation MP.

    Export DV Global Local Stack Pick Intrinsics.
  End Lang.

  Module LangBig (MP: PARAMS_BIG) (M : MemoryModelSpecPrimitives MP).
    Include MP.
    
    (* Handlers *)
    Module Global     := Global.Make MP.
    Module Local      := Local.Make MP.
    Module Stack      := Stack.Make MP.
    Module Intrinsics := Intrinsics.Make MP.
    (* Memory *)
    Include Memory MP M.

    (* Pick handler (depends on memory / concretization) *)
    Include Pick.Make MP.

    (* Denotation *)
    Include Denotation MP.

    Export DV Global Local Stack Pick Intrinsics.
  End LangBig.

  (*
  Module Make (MP : PARAMS) (MMSP : MemoryModelSpecPrimitives MP) (MEM' : Memory MP MMSP) <: Lang MP MMSP.
    Include Lang MP MMSP with Module MEM := MEM'.
End Make.
*)
