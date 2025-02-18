(* TODO: Fix this *)
Unset Universe Checking.

From Vellvm Require Import
  Semantics.LLVMParams
  Semantics.Denotation

  Handlers.Global
  Handlers.Stack
  Handlers.Intrinsics
  Handlers.Pick.

From Mem Require Import
  MemoryModel
  Heaps
  StackFrames
  Addresses.Provenance.

From LLVM_Memory Require Import
  MemBytes
  DvalueBytes
  GepM
  MemoryLLVM.

Import MemoryModel.

(* Handlers.MemoryModel *)
(* Handlers.MemoryInterpreters. *)

Module Type Memory (LP: LLVMParams).
  Import LP.

  Declare Module GEP  : GEPM ADDR IP SIZEOF Events.
  Declare Module Byte : ByteModule ADDR IP SIZEOF Events.
  Declare Module DVALUE_BYTE : DvalueByte LP.

  Module MP := MemoryParams.Make LP GEP Byte DVALUE_BYTE.

  Module H := HEAP_IMPL ADDR.
  Module F := FRAME_LIST ADDR.
  Module FS := FRAME_STACK_LIST ADDR F.

  Include (FULL_CORRECT_MEMORY_MODEL ADDR Byte N_ALLOCATION_ID H F FS).
  Module MEM_HANDLERS := MemoryHandlersCorrect SIZEOF ADDR IP LP.Events Byte (AID: ALLOCATION_ID) (H : HEAP ADDR) (F : FRAME ADDR) (FS : FRAME_STACK ADDR F) (MM : FULL_CORRECT_MEMORY_MODEL ADDR SB AID H F FS).

  Declare Module MMEP : MemoryModelExecPrimitives LP MP.
  Module MEM_MODEL := MakeMemoryModelExec LP MP MMEP.
  Module MEM_SPEC_INTERP := MakeMemorySpecInterpreter LP MP MMEP.MMSP MMEP.MemSpec MMEP.MemExecM.
  Module MEM_EXEC_INTERP := MakeMemoryExecInterpreter LP MP MMEP MEM_MODEL MEM_SPEC_INTERP.

  (* Concretization *)
  Module ByteM := MemBytes.Byte ADDR IP SIZEOF LP.Events MP.BYTE_IMPL.
  Module CP := ConcretizationParams.Make LP MP ByteM.

  Export GEP Byte DVALUE_BYTE MP MEM_MODEL CP.
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
  MemoryHandlersCorrect SIZEOF ADDR IP LP.Events ByteM (SB : ByteModule ADDR IP SIZEOF EVENTS) (AID: ALLOCATION_ID) (H : HEAP ADDR) (F : FRAME ADDR) (FS : FRAME_STACK ADDR F) (MM : FULL_CORRECT_MEMORY_MODEL ADDR SB AID H F FS).
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
