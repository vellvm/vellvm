#!/bin/bash
EXTRACT_DIR=ml/extracted

#Files in which to rewrite
FILENAMES=("InterpretationStack.ml" "InterpretationStack.mli" "TopLevel.ml" "TopLevel.mli")
MEMORYFILES=("MemoryModelImplementation.mli")

function replace () {
    sed -i.bak -e "$1" $EXTRACT_DIR/$2
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
done

for f in "${MEMORYFILES[@]}"
do
    replace "/\([[:space:]]*\)type dvalue = LLVMParamsBigIntptr.Events.DV.dvalue =/{N; s/\([[:space:]]*\)type dvalue = LLVMParamsBigIntptr.Events.DV.dvalue =\([[:space:]]*\)| DVALUE_Addr of ADDR.addr/\1type dvalue = LLVMParamsBigIntptr.Events.DV.dvalue =\2| DVALUE_Addr of LLVMParamsBigIntptr.ADDR.addr/g}" $f
    replace "/\([[:space:]]*\)type uvalue = LLVMParamsBigIntptr.Events.DV.uvalue =/{N; s/\([[:space:]]*\)type uvalue = LLVMParamsBigIntptr.Events.DV.uvalue =\([[:space:]]*\)| UVALUE_Addr of ADDR.addr/\1type uvalue = LLVMParamsBigIntptr.Events.DV.uvalue =\2| UVALUE_Addr of LLVMParamsBigIntptr.ADDR.addr/g}" $f
    replace "/\([[:space:]]*\)type dvalue = LLVMParamsBigIntptr.Events.DV.dvalue =/{N;N;N;N;N;N;s/\(.*\)DVALUE_IPTR of IP.intptr/\1DVALUE_IPTR of LLVMParamsBigIntptr.IP.intptr/g}" $f
    replace "/\([[:space:]]*\)type uvalue = LLVMParamsBigIntptr.Events.DV.uvalue =/{N;N;N;N;N;N;s/\(.*\)UVALUE_IPTR of IP.intptr/\1UVALUE_IPTR of LLVMParamsBigIntptr.IP.intptr/g}" $f
done

# Polymorphism issue
find $EXTRACT_DIR -type f -exec sed -i.bak -e "s/('a1, __) coq_MemPropT coq_Monad/(__, __) coq_MemPropT coq_Monad/g" {} \;
rm -rf $EXTRACT_DIR/*.bak
find $EXTRACT_DIR -type f -exec sed -i.bak -e "s/('a1, ('a1, __) coq_MemPropT) coq_MonadMemState/(__, (__, __) coq_MemPropT) coq_MonadMemState/g" {} \;
rm -rf $EXTRACT_DIR/*.bak
