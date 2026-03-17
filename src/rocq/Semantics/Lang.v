From Vellvm Require Import
     Semantics.Memory.MemBytes
     Semantics.Memory.DvalueBytes
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

    Declare Module GEP  : GEPM LP.
    Declare Module Byte : ByteImpl LP.
    Declare Module DVALUE_BYTE : DvalueByte LP.

    Module MP := MemoryParams.Make LP GEP Byte DVALUE_BYTE.

    Declare Module MMEP : MemoryModelExecPrimitives LP MP.
    Module MEM_MODEL := MakeMemoryModelExec LP MP MMEP.
    Module MEM_SPEC_INTERP := MakeMemorySpecInterpreter LP MP MMEP.MMSP MMEP.MemSpec MMEP.MemExecM.
    Module MEM_EXEC_INTERP := MakeMemoryExecInterpreter LP MP MMEP MEM_MODEL MEM_SPEC_INTERP.

    (* Concretization *)
    Module ByteM := MemBytes.Byte LP MP.BYTE_IMPL.
    Module CP := ConcretizationParams.Make LP MP ByteM.

    Export GEP Byte DVALUE_BYTE MP MEM_MODEL CP.
  End Memory.

  Module Type Lang (LP: LLVMParams).
    Export LP.

    (* Handlers *)
    Module Global     := Global.Make LP.
    Module Local      := Local.Make LP.
    Module Stack      := Stack.Make LP.
    Module Intrinsics := Intrinsics.Make LP.

    (* Memory *)
    Declare Module MEM : Memory LP.
    Export MEM.

    (* Pick handler (depends on memory / concretization) *)
    Module Pick := Pick.Make LP MP ByteM CP.

    (* Denotation *)
    Module D := Denotation LP MP ByteM CP.

    Export DV Global Local Stack Pick Intrinsics
           CP.CONC D.
  End Lang.

  Module Make (LP : LLVMParams) (MEM' : Memory LP) <: Lang LP with Module MEM := MEM'.
    Include Lang LP with Module MEM := MEM'.
  End Make.
