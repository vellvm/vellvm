#!/bin/bash
EXTRACT_DIR=ml/extracted

#Files in which to rewrite
FILENAMES=("InterpretationStack.ml" "InterpretationStack.mli" "TopLevel.ml" "TopLevel.mli")
MEMORYFILES=("MemoryModelImplementation.mli")
BYTEPATCHFILES=("Pick.mli" "Pick.ml" "Denotation.mli" "Denotation.ml")
GENMLIFILES=("GenAlive2.mli")
GENFILES=("GenAlive2.ml")

function replace () {
    perl -i.bak -p0777ne "$1" $EXTRACT_DIR/$2
    rm -rf $EXTRACT_DIR/*.bak
}


for f in "${FILENAMES[@]}"
do
    # BigIntptr mismatches
    replace "s/MemoryModelImplementation.LLVMParamsBigIntptr.Events.DV/LP.Events.DV/g" $f
    replace "s/LLVMParamsBigIntptr.Events.DV/LP.Events.DV/g" $f
    replace "s/MemoryModelImplementation.LLVMParamsBigIntptr.ADDR.addr/LP.ADDR.addr/g" $f
    replace "s/LLVMParamsBigIntptr.ADDR.addr/LP.ADDR.addr/g" $f
    replace "s/MemoryModelImplementation.LLVMParamsBigIntptr.IP/LP.IP/g" $f
    replace "s/LLVMParamsBigIntptr.IP/LP.IP/g" $f
    replace "s/MemoryModelImplementation.LLVMParamsBigIntptr.PROV/LP.PROV/g" $f
    replace "s/LLVMParamsBigIntptr.PROV/LP.PROV/g" $f
    replace "s/MemoryModelImplementation.LLVMParamsBigIntptr.Events/LP.Events/g" $f
    replace "s/LLVMParamsBigIntptr.Events/LP.Events/g" $f
    replace "s/^(\s*)type dvalue_byte = MemoryBigIntptr.CP.CONCBASE.dvalue_byte =\n(\s*)\| DVALUE_ExtractByte of LP.Events.DV.dvalue/\1type dvalue_byte = MemoryBigIntptr.CP.CONCBASE.dvalue_byte =\n\2\| DVALUE_ExtractByte of LLVMParamsBigIntptr.Events.DV.dvalue/gm" $f

    # 64BitIntptr mismatches
    replace "s/MemoryModelImplementation.LLVMParams64BitIntptr.Events.DV/LP.Events.DV/g" $f
    replace "s/LLVMParams64BitIntptr.Events.DV/LP.Events.DV/g" $f
    replace "s/MemoryModelImplementation.LLVMParams64BitIntptr.ADDR.addr/LP.ADDR.addr/g" $f
    replace "s/LLVMParams64BitIntptr.ADDR.addr/LP.ADDR.addr/g" $f
    replace "s/MemoryModelImplementation.LLVMParams64BitIntptr.IP/LP.IP/g" $f
    replace "s/LLVMParams64BitIntptr.IP/LP.IP/g" $f
    replace "s/MemoryModelImplementation.LLVMParams64BitIntptr.PROV/LP.PROV/g" $f
    replace "s/LLVMParams64BitIntptr.PROV/LP.PROV/g" $f
    replace "s/MemoryModelImplementation.LLVMParams64BitIntptr.Events/LP.Events/g" $f
    replace "s/LLVMParams64BitIntptr.Events/LP.Events/g" $f
    replace "s/^(\s*)type dvalue_byte = Memory64BitIntptr.CP.CONCBASE.dvalue_byte =\n(\s*)\| DVALUE_ExtractByte of LP.Events.DV.dvalue/\1type dvalue_byte = Memory64BitIntptr.CP.CONCBASE.dvalue_byte =\n\2\| DVALUE_ExtractByte of LLVMParams64BitIntptr.Events.DV.dvalue/gm" $f

    # Extra stuff
    replace "s/^(\s*)type dvalue_byte = MEM'.CP.CONCBASE.dvalue_byte =\n(\s*)\| DVALUE_ExtractByte of LP.Events.DV.dvalue/\1type dvalue_byte = MEM'.CP.CONCBASE.dvalue_byte =\n\2\| DVALUE_ExtractByte of LP'.Events.DV.dvalue/gm" $f
done

for f in "${MEMORYFILES[@]}"
do
    replace "s/^(\s*)type dvalue = LLVMParamsBigIntptr.Events.DV.dvalue =\n(\s*)\| DVALUE_Addr of ADDR.addr/\1type dvalue = LLVMParamsBigIntptr.Events.DV.dvalue =\n\2\| DVALUE_Addr of LLVMParamsBigIntptr.ADDR.addr/gm" $f
    replace "s/^(\s*)type uvalue = LLVMParamsBigIntptr.Events.DV.uvalue =\n(\s*)\| UVALUE_Addr of ADDR.addr/\1type uvalue = LLVMParamsBigIntptr.Events.DV.uvalue =\n\2\| UVALUE_Addr of LLVMParamsBigIntptr.ADDR.addr/gm" $f
    replace "s/(^\s*type dvalue = LLVMParamsBigIntptr.Events.DV.dvalue =(\n|.)*?DVALUE_IPTR of )IP.intptr/\1LLVMParamsBigIntptr.IP.intptr/gm" $f
    replace "s/(^\s*type uvalue = LLVMParamsBigIntptr.Events.DV.uvalue =(\n|.)*?UVALUE_IPTR of )IP.intptr/\1LLVMParamsBigIntptr.IP.intptr/gm" $f
    replace "s/val ptr_to_int : InfAddr.addr -> coq_Z/val ptr_to_int : ADDR.addr -> coq_Z/g" $f
    replace "s/val ptr_to_int : FinAddr.addr -> coq_Z/val ptr_to_int : ADDR.addr -> coq_Z/g" $f
    replace "s/val address_provenance : InfAddr.addr -> coq_Prov/val address_provenance : ADDR.addr -> coq_Prov/g" $f
    replace "s/val address_provenance : FinAddr.addr -> coq_Prov/val address_provenance : ADDR.addr -> coq_Prov/g" $f
    replace "s/val int_to_ptr : coq_Z -> InfPROV.coq_Prov -> InfAddr.addr coq_OOM/val int_to_ptr : coq_Z -> InfPROV.coq_Prov -> ADDR.addr coq_OOM/g" $f
    replace "s/val int_to_ptr : coq_Z -> FinPROV.coq_Prov -> FinAddr.addr coq_OOM/val int_to_ptr : coq_Z -> FinPROV.coq_Prov -> ADDR.addr coq_OOM/g" $f
done

for f in "${BYTEPATCHFILES[@]}"
do
    replace "s/Byte.int/Integers.Byte.int/g" $f
done

for f in "${GENMLIFILES[@]}"
do
    sed -i "1s/^/open DynamicValues\n/" $EXTRACT_DIR/$f
    sed -i "1s/^/open EitherMonad\n/" $EXTRACT_DIR/$f
    sed -i "/module Int/,/end/d" $EXTRACT_DIR/$f
    sed -i "/module Int1/,/end/d" $EXTRACT_DIR/$f
    sed -i "/module Int8/,/end/d" $EXTRACT_DIR/$f
    sed -i "/module Int32/,/end/d" $EXTRACT_DIR/$f
    sed -i "/module Coq_Int64/,/end/d" $EXTRACT_DIR/$f
    sed -i "/type \(\w\+\) = \1$/d" $EXTRACT_DIR/$f
    replace "s/Int.int/int/g" $f
    replace "s/Int1.int/DynamicValues.int1/g" $f
    replace "s/Int8.int/DynamicValues.int8/g" $f
    replace "s/Int32.int/DynamicValues.int32/g" $f
    replace "s/Coq_Int64.int/DynamicValues.int64/g" $f
    replace "s/Int64.int/DynamicValues.int64/g" $f
    sed -i "/val succ : int -> int/d" $EXTRACT_DIR/$f
    replace "s/coq_VMemintptr/coq_VMemInt_intptr/g" $f
done

for f in "${GENFILES[@]}"
do
    sed -i "1s/^/open DynamicValues\n/" $EXTRACT_DIR/$f
    sed -i "1s/^/open EitherMonad\n/" $EXTRACT_DIR/$f
    replace "s/Pervasives.succ/succ/g" $f
    replace "s/Pervasives.max/max/g" $f
    replace "s/Pervasives.pred/pred/g" $f
    sed -i "/type \(\w\+\) = \1$/d" $EXTRACT_DIR/$f
    sed -i "/let rec \(\w\+\) = \1$/d" $EXTRACT_DIR/$f
    replace "s/Coq_Pos.succ/succ/g" $f
    replace "s/Coq_Z.max/max/g" $f
    replace "s/Coq_Z.min/min/g" $f
    replace "s/Coq_Z.pred/pred/g" $f
    replace "s/Int1.int/DynamicValues.int1/g" $f
    replace "s/Int8.int/DynamicValues.int8/g" $f
    replace "s/Int32.int/DynamicValues.int32/g" $f
    replace "s/Coq_Int64.int/DynamicValues.int64/g" $f
done

# This feels risky. These two are very similar, and only differ because of some newlines in the extraction...
replace "s/^(\s*)type dvalue_byte = MemoryBigIntptr.CP.CONCBASE.dvalue_byte =\n(\s*)\| DVALUE_ExtractByte of LLVMParamsBigIntptr.Events.DV.dvalue \* $/\1type dvalue_byte =\n\2\| DVALUE_ExtractByte of LP.Events.DV.dvalue \* /gm" "InterpretationStack.mli"
replace "s/^(\s*)type dvalue_byte = MemoryBigIntptr.CP.CONCBASE.dvalue_byte =\n(\s*)\| DVALUE_ExtractByte of LLVMParamsBigIntptr.Events.DV.dvalue \* dtyp \* coq_N/\1type dvalue_byte = MEM.CP.CONCBASE.dvalue_byte =\n\2\| DVALUE_ExtractByte of LP.Events.DV.dvalue \* dtyp \* coq_N/gm" "InterpretationStack.mli"

# This feels risky. These two are very similar, and only differ because of some newlines in the extraction...
replace "s/^(\s*)type dvalue_byte = Memory64BitIntptr.CP.CONCBASE.dvalue_byte =\n(\s*)\| DVALUE_ExtractByte of LLVMParams64BitIntptr.Events.DV.dvalue \* $/\1type dvalue_byte =\n\2\| DVALUE_ExtractByte of LP.Events.DV.dvalue \* /gm" "InterpretationStack.mli"
replace "s/^(\s*)type dvalue_byte = Memory64BitIntptr.CP.CONCBASE.dvalue_byte =\n(\s*)\| DVALUE_ExtractByte of LLVMParams64BitIntptr.Events.DV.dvalue \* dtyp \* coq_N/\1type dvalue_byte = MEM.CP.CONCBASE.dvalue_byte =\n\2\| DVALUE_ExtractByte of LP.Events.DV.dvalue \* dtyp \* coq_N/gm" "InterpretationStack.mli"

# Polymorphism issue
find $EXTRACT_DIR -type f -exec sed -i.bak -e "s/('a1, __) coq_MemPropT coq_Monad/(__, __) coq_MemPropT coq_Monad/g" {} \;
rm -rf $EXTRACT_DIR/*.bak
find $EXTRACT_DIR -type f -exec sed -i.bak -e "s/('a1, ('a1, __) coq_MemPropT) coq_MonadMemState/(__, (__, __) coq_MemPropT) coq_MonadMemState/g" {} \;
rm -rf $EXTRACT_DIR/*.bak
rm -rf $EXTRACT_DIR/.DS_Store.bak
rm -rf $EXTRACT_DIR/.DS_Store.*.bak
rm -rf $EXTRACT_DIR/*.orig
