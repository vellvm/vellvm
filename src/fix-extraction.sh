#!/bin/sh
EXTRACT_DIR=ml/extracted

# BigIntptr mismatches.
find $EXTRACT_DIR -type f \( -name "InterpretationStack*" -or -name "TopLevel*" \) -exec sed -i -e "s/MemoryModelImplementation.LLVMParamsBigIntptr.Events.DV/LP.Events.DV/g" {} \;
find $EXTRACT_DIR -type f \( -name "InterpretationStack*" -or -name "TopLevel*" \) -exec sed -i -e "s/LLVMParamsBigIntptr.Events.DV/LP.Events.DV/g" {} \;
find $EXTRACT_DIR -type f \( -name "InterpretationStack*" -or -name "TopLevel*" \) -exec sed -i -e "s/MemoryModelImplementation.LLVMParamsBigIntptr.ADDR.addr/LP.ADDR.addr/g" {} \;
find $EXTRACT_DIR -type f \( -name "InterpretationStack*" -or -name "TopLevel*" \) -exec sed -i -e "s/LLVMParamsBigIntptr.ADDR.addr/LP.ADDR.addr/g" {} \;
find $EXTRACT_DIR -type f \( -name "InterpretationStack*" -or -name "TopLevel*" \) -exec sed -i -e "s/MemoryModelImplementation.LLVMParamsBigIntptr.IP/LP.IP/g" {} \;
find $EXTRACT_DIR -type f \( -name "InterpretationStack*" -or -name "TopLevel*" \) -exec sed -i -e "s/LLVMParamsBigIntptr.IP/LP.IP/g" {} \;
find $EXTRACT_DIR -type f \( -name "InterpretationStack*" -or -name "TopLevel*" \) -exec sed -i -e "s/MemoryModelImplementation.LLVMParamsBigIntptr.PROV/LP.PROV/g" {} \;
find $EXTRACT_DIR -type f \( -name "InterpretationStack*" -or -name "TopLevel*" \) -exec sed -i -e "s/LLVMParamsBigIntptr.PROV/LP.PROV/g" {} \;
find $EXTRACT_DIR -type f \( -name "InterpretationStack*" -or -name "TopLevel*" \) -exec sed -i -e "s/MemoryModelImplementation.LLVMParamsBigIntptr.Events/LP.Events/g" {} \;
find $EXTRACT_DIR -type f \( -name "InterpretationStack*" -or -name "TopLevel*" \) -exec sed -i -e "s/LLVMParamsBigIntptr.Events/LP.Events/g" {} \;

# 64BitIntptr mismatches
find $EXTRACT_DIR -type f \( -name "InterpretationStack*" -or -name "TopLevel*" \) -exec sed -i -e "s/MemoryModelImplementation.LLVMParams64BitIntptr.Events.DV/LP.Events.DV/g" {} \;
find $EXTRACT_DIR -type f \( -name "InterpretationStack*" -or -name "TopLevel*" \) -exec sed -i -e "s/LLVMParams64BitIntptr.Events.DV/LP.Events.DV/g" {} \;
find $EXTRACT_DIR -type f \( -name "InterpretationStack*" -or -name "TopLevel*" \) -exec sed -i -e "s/MemoryModelImplementation.LLVMParams64BitIntptr.ADDR.addr/LP.ADDR.addr/g" {} \;
find $EXTRACT_DIR -type f \( -name "InterpretationStack*" -or -name "TopLevel*" \) -exec sed -i -e "s/LLVMParams64BitIntptr.ADDR.addr/LP.ADDR.addr/g" {} \;
find $EXTRACT_DIR -type f \( -name "InterpretationStack*" -or -name "TopLevel*" \) -exec sed -i -e "s/MemoryModelImplementation.LLVMParams64BitIntptr.IP/LP.IP/g" {} \;
find $EXTRACT_DIR -type f \( -name "InterpretationStack*" -or -name "TopLevel*" \) -exec sed -i -e "s/LLVMParams64BitIntptr.IP/LP.IP/g" {} \;
find $EXTRACT_DIR -type f \( -name "InterpretationStack*" -or -name "TopLevel*" \) -exec sed -i -e "s/MemoryModelImplementation.LLVMParams64BitIntptr.PROV/LP.PROV/g" {} \;
find $EXTRACT_DIR -type f \( -name "InterpretationStack*" -or -name "TopLevel*" \) -exec sed -i -e "s/LLVMParams64BitIntptr.PROV/LP.PROV/g" {} \;
find $EXTRACT_DIR -type f \( -name "InterpretationStack*" -or -name "TopLevel*" \) -exec sed -i -e "s/MemoryModelImplementation.LLVMParams64BitIntptr.Events/LP.Events/g" {} \;
find $EXTRACT_DIR -type f \( -name "InterpretationStack*" -or -name "TopLevel*" \) -exec sed -i -e "s/LLVMParams64BitIntptr.Events/LP.Events/g" {} \;

# Polymorphism issue
find $EXTRACT_DIR -type f -exec sed -i -e "s/('a1, __) coq_MemPropT coq_Monad/(__, __) coq_MemPropT coq_Monad/g" {} \;
find $EXTRACT_DIR -type f -exec sed -i -e "s/('a1, ('a1, __) coq_MemPropT) coq_MonadMemState/(__, (__, __) coq_MemPropT) coq_MonadMemState/g" {} \;
