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

join_strings() {
  local delimiter="$1"
  shift
  local joined=""
  
  for string in "$@"; do
      joined+="$string$delimiter"
  done

  echo "${joined%"$delimiter"}"
}


GEN_OPEN_MODULES=("open LLVMAst" "open Bits" "open Binary" "open BinNums" "open BinPos" "open BinNat" "open Floats" "open Integers" "open VellvmIntegers" "open EitherMonad" "open DynamicValues" "open DynamicTypes" "open CeresS" "open Error" "open Datatypes" "open Decimal" "open Nat" "open CeresString" "open AstLib" "open ShowAST")
GEN_MODULES_DECLARATION=$(join_strings "\n" "${GEN_OPEN_MODULES[@]}")
# for string in "${GEN_OPEN_MODULESS[@]}"; do
#     echo "$string"
# done
# echo "${GEN_MODULES_DECLARATION}"
# echo "This is successful"

for f in "${GENMLIFILES[@]}"
do
    sed -i "1s/^/${GEN_MODULES_DECLARATION}\n/" $EXTRACT_DIR/$f
    # sed -i "1s/^/open Error\n/" $EXTRACT_DIR/$f
    # sed -i "1s/^/open CeresS\n/" $EXTRACT_DIR/$f
    # sed -i "1s/^/open DynamicTypes\n/" $EXTRACT_DIR/$f
    # sed -i "1s/^/open DynamicValues\n/" $EXTRACT_DIR/$f
    # sed -i "1s/^/open EitherMonad\n/" $EXTRACT_DIR/$f
    # sed -i "1s/^/open VellvmIntegers\n/" $EXTRACT_DIR/$f
    # sed -i "1s/^/open BinNums\n/" $EXTRACT_DIR/$f
    # sed -i "1s/^/open BinPos\n/" $EXTRACT_DIR/$f
    # sed -i "1s/^/open BinNat\n/" $EXTRACT_DIR/$f
    # sed -i "1s/^/open Integers\n/" $EXTRACT_DIR/$f
    # sed -i "1s/^/module LLVMAst = LLVMAst\n/" $EXTRACT_DIR/$f
    # sed -i "1s/^/open Binary\n/" $EXTRACT_DIR/$f
    # sed -i "1s/^/open Bits\n/" $EXTRACT_DIR/$f
    # sed -i "1s/^/open Floats\n/" $EXTRACT_DIR/$f
    sed -i "/module Int/,/end/d" $EXTRACT_DIR/$f
    sed -i "/module Int1/,/end/d" $EXTRACT_DIR/$f
    sed -i "/module Int8/,/end/d" $EXTRACT_DIR/$f
    sed -i "/module Int32/,/end/d" $EXTRACT_DIR/$f
    sed -i "/module Coq_Int64/,/end/d" $EXTRACT_DIR/$f
    sed -i "/type \(\w\+\) = \1$/d" $EXTRACT_DIR/$f
    
    sed -i "/^type positive =/,/^$/c\type positive = BinNums.positive\n" $EXTRACT_DIR/$f
    sed -i "/^type n =/,/^$/c\type n = BinNums.coq_N\n" $EXTRACT_DIR/$f
    sed -i "/^type z =/,/^$/c\type z = BinNums.coq_Z\n" $EXTRACT_DIR/$f
    sed -i "/^module Pos :/,/end/c\module Pos = BinPos.Pos" $EXTRACT_DIR/$f
    sed -i "/^module Coq_Pos :/,/end/c\module Coq_Pos = Pos" $EXTRACT_DIR/$f
    sed -i "/^module N :/,/end/c\module N = BinNat.N" $EXTRACT_DIR/$f
    sed -i "/^module Z :/,/end/c\module Z = BinInt.Z" $EXTRACT_DIR/$f
    sed -i "/^module Coq_Z :/,/end/c\module Coq_Z = Z" $EXTRACT_DIR/$f
    sed -i "/^module WORDSIZE :/,/end/c\module WORDSIZE = Integers.WORDSIZE" $EXTRACT_DIR/$f
    sed -i "/^module Make/,/end/c\module Make = Integers.Make" $EXTRACT_DIR/$f
    sed -i "/^module Wordsize_32/,/end/c\module Wordsize_32 = Integers.Wordsize_32" $EXTRACT_DIR/$f
    sed -i "/^module Wordsize_64/,/end/c\module Wordsize_64 = Integers.Wordsize_64" $EXTRACT_DIR/$f
    sed -i "/^type binary_float =/,/^$/c\type binary_float = Binary.binary_float\n" $EXTRACT_DIR/$f

    # LLVMAst replacement
    sed -i "/^type raw_id =/,/^$/c\type raw_id = LLVMAst.raw_id\n" $EXTRACT_DIR/$f
    sed -i "/^type ident =/,/^$/c\type ident = LLVMAst.ident\n" $EXTRACT_DIR/$f
    sed -i "/^type typ =/,/^$/c\type typ = LLVMAst.typ\n" $EXTRACT_DIR/$f
    sed -i "/^type icmp =/,/^$/c\type icmp = LLVMAst.icmp\n" $EXTRACT_DIR/$f
    sed -i "/^type fcmp =/,/^$/c\type fcmp = LLVMAst.fcmp\n" $EXTRACT_DIR/$f
    sed -i "/^type ibinop =/,/^$/c\type ibinop = LLVMAst.ibinop\n" $EXTRACT_DIR/$f
    sed -i "/^type fbinop =/,/^$/c\type fbinop = LLVMAst.fbinop\n" $EXTRACT_DIR/$f
    sed -i "/^type fast_math =/,/^$/c\type fast_math = LLVMAst.fast_math\n" $EXTRACT_DIR/$f
    sed -i "/^type conversion_type =/,/^$/c\type conversion_type = LLVMAst.conversion_type\n" $EXTRACT_DIR/$f
    sed -i "/^type 't block =/,/^$/c\type 't block = 't LLVMAst.block\n" $EXTRACT_DIR/$f
    sed -i "/^type instr_id =/,/^$/c\type instr_id = LLVMAst.instr_id\n" $EXTRACT_DIR/$f
    sed -i "/^type 't terminator =/,/^$/c\type 't terminator = 't LLVMAst.terminator\n" $EXTRACT_DIR/$f
    sed -i "/^type 't code =/,/^$/c\type 't code = 't LLVMAst.code\n" $EXTRACT_DIR/$f

    # CeresS replacement
    sed -i "/^type 'a sexp_ =/,/^$/c\type 'a sexp_ = 'a CeresS.sexp_\n" $EXTRACT_DIR/$f
    sed -i "/^type atom =/,/^$/c\type atom = CeresS.atom\n" $EXTRACT_DIR/$f

    # DynamicTypes replacement
    sed -i "/^type dtyp =/,/^$/c\type dtyp = DynamicTypes.dtyp\n" $EXTRACT_DIR/$f

    # VellvmIntegers
    sed -i "/^type 'i vMemInt/,/^$/c\type 'i vMemInt = 'i VellvmIntegers.coq_VMemInt\n" $EXTRACT_DIR/$f

    # Error
    sed -i "/^type 'a oOM/,/^$/c\type 'a oOM = 'a Error.coq_OOM\n" $EXTRACT_DIR/$f

    # Datatypes
    sed -i "/^type nat /,/^$/c\type nat = Datatypes.nat\n" $EXTRACT_DIR/$f
    # sed -i "/^type ('a, 'b) sum /,/^$/c\type ('a, 'b) sum = ('a, 'b) Datatypes.sum\n" $EXTRACT_DIR/$f
    sed -i "/^type comparison /,/^$/c\type comparison = Datatypes.comparison\n" $EXTRACT_DIR/$f
    
    # Binary
    sed -i "/^type binary_float0/,/^$/c\type binary_float0 = Binary.binary_float\n" $EXTRACT_DIR/$f
    
    # DynamicValues replacemeent
    sed -i "/^module Wordsize1/,/end/c\module Wordsize1 = DynamicValues.Wordsize1" $EXTRACT_DIR/$f
    sed -i "/^module Wordsize8/,/end/c\module Wordsize8 = DynamicValues.Wordsize8" $EXTRACT_DIR/$f
    
    sed -i 's/^module Int\([0-9]\+\) =.*$/module Int\1 = DynamicValues.Int\1/' $EXTRACT_DIR/$f
    sed -i 's/^module \(Coq_Int64\) =.*$/module \1 = DynamicValues.Int64/' $EXTRACT_DIR/$f
    sed -i 's/^type int\([1-9]\+\) =.*$/type int\1 = DynamicValues.int\1/' $EXTRACT_DIR/$f
    
    # replace "s/Int.int/int/g" $f
    # replace "s/Int1.int/DynamicValues.int1/g" $f
    # replace "s/Int8.int/DynamicValues.int8/g" $f
    # replace "s/Int32.int/DynamicValues.int32/g" $f
    replace "s/Coq_Int64.int/DynamicValues.int64/g" $f
    # replace "s/Int64.int/DynamicValues.int64/g" $f
    sed -i "/val succ : int -> int/d" $EXTRACT_DIR/$f
    replace "s/coq_VMemintptr/coq_VMemInt_intptr/g" $f

    sed -i "/^type uint =/,/^$/c\type uint = Decimal.uint\n" $EXTRACT_DIR/$f
    sed -i '/^type uint .*$/,/type positive/{//!d}' $EXTRACT_DIR/$f
    sed -i '/^module Wordsize_64 .*$/,/type binary_float /{//!d}' $EXTRACT_DIR/$f
    sed -i '/type binary_float .*/,/type binary_float0 .*$/{//!d}' $EXTRACT_DIR/$f
    sed -i '/type binary_float0 .*/,/type binary32 .*$/{//!d}' $EXTRACT_DIR/$f
    sed -i '/type binary32 .*/,/type binary64 .*$/{//!d}' $EXTRACT_DIR/$f
    sed -i '/type binary64 .*/,/type float .*$/{//!d}' $EXTRACT_DIR/$f
    sed -i '/type float32 .*/,/type int0 .*$/{//!d}' $EXTRACT_DIR/$f
    sed -i '/val show_dtyp /,/val fT_Rounding .*$/d' $EXTRACT_DIR/$f
    sed -i '/val compb .*/,/val string_of_Z .*$/{//!d}' $EXTRACT_DIR/$f
    sed -i '/val serialize_ibinop .*/,/val serialize_fcmp .*$/d' $EXTRACT_DIR/$f
    sed -i '/module Coq_NilEmpty .*/,/end/d' $EXTRACT_DIR/$f
    sed -i '/module DVALUE .*/,/ end/d' $EXTRACT_DIR/$f
    sed -i '/val uvalue_measure .*/,/val uvalue_constructor_string/d' $EXTRACT_DIR/$f
done

for f in "${GENFILES[@]}"
do
    sed -i "1s/^/${GEN_MODULES_DECLARATION}\n/" $EXTRACT_DIR/$f
    # sed -i "1s/^/open Error\n/" $EXTRACT_DIR/$f
    # sed -i "1s/^/open CeresS\n/" $EXTRACT_DIR/$f
    # sed -i "1s/^/open DynamicTypes\n/" $EXTRACT_DIR/$f
    # sed -i "1s/^/open DynamicValues\n/" $EXTRACT_DIR/$f
    # sed -i "1s/^/open EitherMonad\n/" $EXTRACT_DIR/$f
    # sed -i "1s/^/open VellvmIntegers\n/" $EXTRACT_DIR/$f
    # sed -i "1s/^/open BinNums\n/" $EXTRACT_DIR/$f
    # sed -i "1s/^/open BinPos\n/" $EXTRACT_DIR/$f
    # sed -i "1s/^/open BinNat\n/" $EXTRACT_DIR/$f
    # sed -i "1s/^/module LLVMAst = LLVMAst\n/" $EXTRACT_DIR/$f
    # sed -i "1s/^/open Integers\n/" $EXTRACT_DIR/$f
    # sed -i "1s/^/open Binary\n/" $EXTRACT_DIR/$f
    # sed -i "1s/^/open Bits\n/" $EXTRACT_DIR/$f
    # sed -i "1s/^/open Floats\n/" $EXTRACT_DIR/$f

    
    replace "s/Pervasives.succ/succ/g" $f
    replace "s/Pervasives.max/max/g" $f
    replace "s/Pervasives.pred/pred/g" $f
    sed -i "/type \(\w\+\) = \1$/d" $EXTRACT_DIR/$f
    sed -i "/let rec \(\w\+\) = \1$/d" $EXTRACT_DIR/$f
    replace "s/Coq_Pos.succ/succ/g" $f
    replace "s/Coq_Z.max/max/g" $f
    replace "s/Coq_Z.min/min/g" $f
    replace "s/Coq_Z.pred/pred/g" $f
    sed -i "/^type positive =/,/^$/c\type positive = BinNums.positive\n" $EXTRACT_DIR/$f
    sed -i "/^type n =/,/^$/c\type n = BinNums.coq_N\n" $EXTRACT_DIR/$f
    sed -i "/^type z =/,/^$/c\type z = BinNums.coq_Z\n" $EXTRACT_DIR/$f
    sed -i "/^module Pos =/,/end/c\module Pos = BinPos.Pos" $EXTRACT_DIR/$f
    sed -i "/^module Coq_Pos =/,/end/c\module Coq_Pos = Pos" $EXTRACT_DIR/$f
    sed -i "/^module N =/,/end/c\module N = BinNat.N" $EXTRACT_DIR/$f
    sed -i "/^module Z =/,/end/c\module Z = BinInt.Z" $EXTRACT_DIR/$f
    sed -i "/^module Coq_Z =/,/end/c\module Coq_Z = Z" $EXTRACT_DIR/$f
    sed -i "/^module WORDSIZE =/,/end/c\module WORDSIZE = Integers.WORDSIZE" $EXTRACT_DIR/$f
    sed -i "/^module Make =/,/end/c\module Make = Integers.Make" $EXTRACT_DIR/$f
    sed -i "/^module Wordsize_32 =/,/end/c\module Wordsize_32 = Integers.Wordsize_32" $EXTRACT_DIR/$f
    sed -i 's/^module Int =.*$/module Int = Integers.Int/' $EXTRACT_DIR/$f
    sed -i "/^module Wordsize_64 =/,/end/c\module Wordsize_64 = Integers.Wordsize_64" $EXTRACT_DIR/$f
    sed -i "/^module Int64 =/,/end/c\module Int64 = Int64" $EXTRACT_DIR/$f
    sed -i "/^type binary_float =/,/^$/c\type binary_float = Binary.binary_float\n" $EXTRACT_DIR/$f

    # LLVMAst replacement
    sed -i "/^type raw_id =/,/^$/c\type raw_id = LLVMAst.raw_id\n" $EXTRACT_DIR/$f
    sed -i "/^type ident =/,/^$/c\type ident = LLVMAst.ident\n" $EXTRACT_DIR/$f
    sed -i "/^type typ =/,/^$/c\type typ = LLVMAst.typ\n" $EXTRACT_DIR/$f
    sed -i "/^type icmp =/,/^$/c\type icmp = LLVMAst.icmp\n" $EXTRACT_DIR/$f
    sed -i "/^type fcmp =/,/^$/c\type fcmp = LLVMAst.fcmp\n" $EXTRACT_DIR/$f
    sed -i "/^type ibinop =/,/^$/c\type ibinop = LLVMAst.ibinop\n" $EXTRACT_DIR/$f
    sed -i "/^type fbinop =/,/^$/c\type fbinop = LLVMAst.fbinop\n" $EXTRACT_DIR/$f
    sed -i "/^type fast_math =/,/^$/c\type fast_math = LLVMAst.fast_math\n" $EXTRACT_DIR/$f
    sed -i "/^type conversion_type =/,/^$/c\type conversion_type = LLVMAst.conversion_type\n" $EXTRACT_DIR/$f
    sed -i "/^type 't block =/,/^$/c\type 't block = 't LLVMAst.block\n" $EXTRACT_DIR/$f
    sed -i "/^type instr_id =/,/^$/c\type instr_id = LLVMAst.instr_id\n" $EXTRACT_DIR/$f
    sed -i "/^type 't terminator =/,/^$/c\type 't terminator = 't LLVMAst.terminator\n" $EXTRACT_DIR/$f
    sed -i "/^type 't code =/,/^$/c\type 't code = 't LLVMAst.code\n" $EXTRACT_DIR/$f

    #AstLib replacement
    sed -i "/^module RawIDOrd =/,/end/c\module RawIDOrd = AstLib.RawIDOrd" $EXTRACT_DIR/$f
    sed -i "/^module IdentDec =/,/end/c\module IdentDec = AstLib.IdentDec" $EXTRACT_DIR/$f
    sed -i "/^module Ident =/,/^$/c\module Ident = AstLib.Ident\n" $EXTRACT_DIR/$f
    
    # CeresS replacement
    sed -i "/^type 'a sexp_ =/,/^$/c\type 'a sexp_ = 'a CeresS.sexp_\n" $EXTRACT_DIR/$f
    sed -i "/^type atom =/,/^$/c\type atom = CeresS.atom\n" $EXTRACT_DIR/$f

    # DynamicTypes replacement
    sed -i "/^type dtyp =/,/^$/c\type dtyp = DynamicTypes.dtyp\n" $EXTRACT_DIR/$f

    # VellvmIntegers
    sed -i "/^type 'i vMemInt/,/^$/c\type 'i vMemInt = 'i VellvmIntegers.coq_VMemInt\n" $EXTRACT_DIR/$f

    # Error
    sed -i "/^type 'a oOM/,/^$/c\type 'a oOM = 'a Error.coq_OOM\n" $EXTRACT_DIR/$f

    # Datatypes
    sed -i "/^type nat /,/^$/c\type nat = Datatypes.nat\n" $EXTRACT_DIR/$f
    # sed -i "/^type ('a, 'b) sum /,/^$/c\type ('a, 'b) sum = ('a, 'b) Datatypes.sum\n" $EXTRACT_DIR/$f
    sed -i "/^type comparison /,/^$/c\type comparison = Datatypes.comparison\n" $EXTRACT_DIR/$f

    # Binary
    sed -i "/^type binary_float0/,/^$/c\type binary_float0 = Binary.binary_float\n" $EXTRACT_DIR/$f
    
    # DynamicValues replacemeent
    sed -i "/^module Wordsize1 =/,/end/c\module Wordsize1 = DynamicValues.Wordsize1" $EXTRACT_DIR/$f
    sed -i "/^module Wordsize8 =/,/end/c\module Wordsize8 = DynamicValues.Wordsize8" $EXTRACT_DIR/$f
    sed -i 's/^module Int\([0-9]\+\) =.*$/module Int\1 = DynamicValues.Int\1/' $EXTRACT_DIR/$f
    sed -i 's/^module \(Coq_Int64\) =.*$/module \1 = DynamicValues.Int64/' $EXTRACT_DIR/$f
    sed -i 's/^type int\([1-9]\+\) =.*$/type int\1 = DynamicValues.int\1/' $EXTRACT_DIR/$f
    sed -i "/let randomRInt = /ilet rec coqPositiveToInt = function\n| Coq_xI p0 -> 2 * (coqPositiveToInt p0) + 1\n| Coq_xO p0 -> 2 * (coqPositiveToInt p0)\n| Coq_xH -> 1\n\nlet coqZToInt  = function\n| Z0 -> 0\n| Zpos p -> coqPositiveToInt p\n| Zneg p -> ~-(coqPositiveToInt p)\n\nlet rec nonNegIntToCoqPositive y =\nmatch y with\n| 0 -> Coq_xH\n| 1 -> Coq_xH\n| _ -> if (y mod 2 > 0) then Coq_xI (nonNegIntToCoqPositive (y / 2 - 1)) else Coq_xO (nonNegIntToCoqPositive (y / 2))\n\nlet intToCoqZ x =\nif (x < 0) then Zneg (nonNegIntToCoqPositive ~-x) else if (x > 0) then Zpos (nonNegIntToCoqPositive x) else Z0\n\n" $EXTRACT_DIR/$f

    sed -i "/let randomRN = /ilet coqNToInt = function\n| N0 -> 0\n| Npos p -> coqPositiveToInt p\n\nlet intToCoqN x =\nif (x < 0) then Npos (nonNegIntToCoqPositive ~-x) else if (x > 0) then Npos (nonNegIntToCoqPositive x) else N0\n\n" $EXTRACT_DIR/$f

    # sed -i "/let listOf g =/,/^$/c\let listOf g = \nGenLow__0.sized (fun n0 -> \nGenLow__0.bindGen (GenLow__0.choose chooseNat (0, coqZToInt n0)) (fun k -> \nvectorOf k g))\n\n" $EXTRACT_DIR/$f
    # sed -i "/let suchThatMaybe g p =/,/^$/c\let suchThatMaybe g p = \nGenLow__0.sized (fun n0 -> retry (coqZToInt n0) (suchThatMaybe1 g p))\n\n" $EXTRACT_DIR/$f
    # sed -i "/let suchThatMaybeOpt g p =/,/^$/c\  let suchThatMaybeOpt g p = \nGenLow__0.sized (fun n0 -> \nretry (coqZToInt n0) \n(GenLow__0.fmap (fun x -> \nmatch x with \n| Some a -> if p a then Some a else None\n| None -> None) g))\n" $EXTRACT_DIR/$f
    # sed -i "/let sample/,/^$/c\let sample (g : 'a1 coq_G) : 'a1 list = \nlet l = combine (rnds newRandomSeed 10) (createRange 10 []) in \nmap (fun p -> let (r, n0) = p in g (intToCoqZ n0) r) l\n" $EXTRACT_DIR/$f
    
    replace "s/XO/Coq_xO/g" $f
    replace "s/XH/Coq_xH/g" $f
    replace "s/XI/Coq_xI/g" $f
    replace "s/TYPE_I i/LLVMAst.TYPE_I i/g" $f
    replace "s/Raw0/Raw/g" $f
    # replace "s/Int1.int/DynamicValues.int1/g" $f
    # replace "s/Int8.int/DynamicValues.int8/g" $f
    # replace "s/Int32.int/DynamicValues.int32/g" $f
    # replace "s/Coq_Int64.int/DynamicValues.int64/g" $f

    sed -i "/^type uint =/,/^$/c\type uint = Decimal.uint\n" $EXTRACT_DIR/$f
    sed -i '/^type uint .*$/,/(\*\* val compose/{//!d}' $EXTRACT_DIR/$f
    sed -i '/(\*\* val eqb .*$/,/type positive .*$/{//!d}' $EXTRACT_DIR/$f
    sed -i '/module Int64 .*$/,/type binary_float .*$/{//!d}' $EXTRACT_DIR/$f
    sed -i '/type binary_float .*/,/type binary_float0 .*$/{//!d}' $EXTRACT_DIR/$f
    sed -i '/type binary_float0 .*/,/type binary32 .*$/{//!d}' $EXTRACT_DIR/$f
    sed -i '/type binary32 .*/,/type binary64 .*$/{//!d}' $EXTRACT_DIR/$f
    sed -i '/type binary64 .*/,/type float .*$/{//!d}' $EXTRACT_DIR/$f
    sed -i '/type float32 .*/,/type int0 .*$/{//!d}' $EXTRACT_DIR/$f
    sed -i '/(\*\* val eqb_ascii .*/,/(\*\* val string_of_Z .*$/{//!d}' $EXTRACT_DIR/$f
    sed -i '/(\*\* val serialize_ibinop .*/,/type dtyp .*$/{//!d}' $EXTRACT_DIR/$f
    sed -i '/module Coq_NilEmpty .*/,/end/d' $EXTRACT_DIR/$f
    replace "s/Coq_NilEmpty/NilEmpty/g" $f
    sed -i '/(\*\* val double_to_hex_string .*/,/module Wordsize1 .*$/{//!d}' $EXTRACT_DIR/$f
    sed -i '/module DVALUE .*/,/ end/d' $EXTRACT_DIR/$f
    replace "s/B754_finite0/B754_finite/g" $f

    # Annotation
    sed -i "/let coq_STGST =/c\let coq_STGST : (coq_GenState, __ GenLow.coq_G, __) stateT monad =" $EXTRACT_DIR/$f
    sed -i "/let coq_MGEN =/c\let coq_MGEN :  __ coq_GenALIVE2 monad =" $EXTRACT_DIR/$f
    sed -i "/let gen_float32 =/c\let gen_float32 : float32 coq_GenALIVE2 =" $EXTRACT_DIR/$f
    sed -i "/let gen_float32 =/c\let gen_float32 : float32 coq_GenALIVE2 =" $EXTRACT_DIR/$f
    sed -i "/let gen_tester =/c\let gen_tester:  (typ, typ block * typ block list) toplevel_entity list coq_GenALIVE2 =" $EXTRACT_DIR/$f
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
