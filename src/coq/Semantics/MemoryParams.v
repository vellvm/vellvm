From Vellvm Require Import
     Semantics.LLVMParams
     Semantics.GepM
     Semantics.Memory.MemBytes.

Module Type _MEMORY_PARAMS (LLVMParams : LLVM_PARAMS).
  Declare Module GEP : GEPM LLVMParams.
  Module ByteImpl := SByteM LLVMParams.  
End _MEMORY_PARAMS.

Module Type PARAMS := LLVM_PARAMS <+ _MEMORY_PARAMS.
Module Type PARAMS_BIG := LLVM_PARAMS_BIG <+ _MEMORY_PARAMS.

Module Make (LLVMParams : LLVM_PARAMS) <: PARAMS.
  Include LLVMParams.
  Module GEP := GepM.Make LLVMParams.
  Module ByteImpl := SByteM LLVMParams.
End Make.

Module MakeBig (LLVMParams : LLVM_PARAMS_BIG) <: PARAMS_BIG.
  Include LLVMParams.
  Module GEP := GepM.Make LLVMParams.
  Module ByteImpl := SByteM LLVMParams.
End MakeBig.
