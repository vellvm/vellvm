From Vellvm Require Import
     Semantics.Memory.MemBytes
     Semantics.LLVMParams
     Semantics.GepM
     Semantics.Denotation

     Handlers.Global
     Handlers.Stack
     Handlers.Intrinsics
     Handlers.Pick
     Handlers.MemoryModel
     Handlers.MemoryInterpreters.

  Module Type Memory (LP: LLVMParams).
    Import LP.

    Declare Module GEP  : GEPM ADDR PTOI PROV ITOP IP SIZEOF Events.
    Declare Module Byte : ByteImpl ADDR IP SIZEOF Events.

    Module MP := MemoryParams.Make LP GEP Byte.

    Declare Module MMEP : MemoryModelExecPrimitives LP MP.
    Module MEM_MODEL := MakeMemoryModelExec LP MP MMEP.
    Module MEM_SPEC_INTERP := MakeMemorySpecInterpreter LP MP MMEP.MMSP MMEP.MemSpec MMEP.MemExecM.
    Module MEM_EXEC_INTERP := MakeMemoryExecInterpreter LP MP MMEP MEM_MODEL MEM_SPEC_INTERP.

    (* Concretization *)
    Module ByteM := MemBytes.Byte ADDR IP SIZEOF LP.Events MP.BYTE_IMPL.
    Module CP := ConcretizationParams.Make LP MP ByteM.

    Export GEP Byte MP MEM_MODEL CP.
  End Memory.

  Module Type Lang (LP: LLVMParams).
    Export LP.

    (* Handlers *)
    Module Global     := Global.Make ADDR IP SIZEOF LP.Events.
    Module Local      := Local.Make ADDR IP SIZEOF LP.Events.
    Module Stack      := Stack.Make ADDR IP SIZEOF LP.Events.
    Module Intrinsics := Intrinsics.Make ADDR IP SIZEOF LP.Events.

    (* Memory *)
    Declare Module MEM : Memory LP.
    Export MEM.

    (* Pick handler (depends on memory / concretization) *)
    Module Pick := Pick.Make LP MP ByteM CP.

    (* Denotation *)
    Module D := Denotation LP MP ByteM CP.

    Export Events Events.DV Global Local Stack Pick Intrinsics
           CP.CONC D.
  End Lang.

  Module Make (LP : LLVMParams) (MEM' : Memory LP) <: Lang LP with Module MEM := MEM'.
    Include Lang LP with Module MEM := MEM'.
  End Make.
