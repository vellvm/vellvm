declare  i32 @puts()

@g0 = global <{i8, <{<{<{<{float, float, i1}>}>, <{{i64, i32, i1, i64}, <{i64, i32}>, <2 x float>, <2 x i1>, <{i8, i32, i8}>}>, <{<{i1}>, <{i64, i1}>}>, {i32, float, float, i64}*, {{i1, i32, i32}, {i8}, <6 x i64>, <2 x float>}}>, <2 x i1>}>}> <{i8 0, <{<{<{<{float, float, i1}>}>, <{{i64, i32, i1, i64}, <{i64, i32}>, <2 x float>, <2 x i1>, <{i8, i32, i8}>}>, <{<{i1}>, <{i64, i1}>}>, {i32, float, float, i64}*, {{i1, i32, i32}, {i8}, <6 x i64>, <2 x float>}}>, <2 x i1>}> <{<{<{<{float, float, i1}>}>, <{{i64, i32, i1, i64}, <{i64, i32}>, <2 x float>, <2 x i1>, <{i8, i32, i8}>}>, <{<{i1}>, <{i64, i1}>}>, {i32, float, float, i64}*, {{i1, i32, i32}, {i8}, <6 x i64>, <2 x float>}}> <{<{<{float, float, i1}>}> <{<{float, float, i1}> <{float 0xb7dac08800000000, float 0x3f74c364c0000000, i1 0}>}>, <{{i64, i32, i1, i64}, <{i64, i32}>, <2 x float>, <2 x i1>, <{i8, i32, i8}>}> <{{i64, i32, i1, i64} {i64 18446744073709551611, i32 4294967292, i1 1, i64 18446744073709551614}, <{i64, i32}> <{i64 4, i32 4294967293}>, <2 x float> <float 0x37e49c2b00000000, float 0xbeaa9b2e60000000>, <2 x i1> <i1 1, i1 1>, <{i8, i32, i8}> <{i8 252, i32 4294967291, i8 255}>}>, <{<{i1}>, <{i64, i1}>}> <{<{i1}> <{i1 0}>, <{i64, i1}> <{i64 3, i1 1}>}>, {i32, float, float, i64}* @g1, {{i1, i32, i32}, {i8}, <6 x i64>, <2 x float>} {{i1, i32, i32} {i1 0, i32 4294967293, i32 4294967294}, {i8} {i8 0}, <6 x i64> <i64 18446744073709551612, i64 3, i64 5, i64 18446744073709551612, i64 5, i64 4>, <2 x float> <float 0x39ac99c800000000, float 0xbded563620000000>}}>, <2 x i1> <i1 0, i1 1>}>}> 

@g2 = global <6 x i1> <i1 0, i1 1, i1 1, i1 0, i1 1, i1 1> 

@g3 = global <5 x i1> <i1 1, i1 0, i1 1, i1 1, i1 1> 

@g1 = global {i32, float, float, i64} {i32 4294967293, float 0xc6925c06c0000000, float 0x456562ad80000000, i64 4} 

define  i64 @g4(<{{[2 x i64]*, {<6 x float>, float*}, <{<5 x i1>, {i32, i1, i32}, <{i32, i8, i1, i8, i8}>, <{i64, i8}>, <{i1, i64}>}>, <{float*, [1 x i8]}>, <{<4 x i8>, i8*, <{i32, i64, i1, i64, float}>, <{i64, float, i32}>, {float, float, i64, i32}}>}*, {{<2 x i1>, {{i32, i64, i8}, [2 x i1], [1 x i32]}, <2 x float>}}}> %v5, {[3 x i32], {<{i8}>, <{i64, i64, i32, i8, i8}>}, {<{float, i64}>, <{i32, i1}>, i32*}}** %v6, <{<{<{<5 x i1>}>, <4 x i64>, <{{<4 x i1>, {i32, float}, <{i64, i1, i8, float}>, {i32, i8, i64, i64}, <{i64, i32, i32}>}, i32, <{i1*, {i1, i1}, [2 x i1], <1 x i8>}>, i1*, {{i1, float, i8, float}}}>, <{i32, <{<{i32}>, {i32, i64, float, i8}}>}>}>}> %v7, [0 x [1 x <{<5 x i32>}>]] %v8, <{<{<4 x float>, <{{<5 x float>, <{i1, i64, i64}>, i1*, <2 x i32>}, [0 x {float}], <{{i1, i1}, <{float, float, i8, float}>, {i64}, <{i64}>}>, <{[2 x i64]}>, <4 x i64>}>, <{{<{i64, i64, i64, i1, float}>, <{float, i64}>}}>, {<{{i32, i64, i1, i8, i64}, {i32, i64, i1}, {i1, i64, i8}, <{i32, i8, i8, i8, float}>, {i32, i8, i1, float, i1}}>, <2 x i1>}}>, <5 x float>}> %v9) {
b10:
    %v11 = ptrtoint <5 x i1>* @g3 to i64
    %v12 = extractvalue <{<{<4 x float>, <{{<5 x float>, <{i1, i64, i64}>, i1*, <2 x i32>}, [0 x {float}], <{{i1, i1}, <{float, float, i8, float}>, {i64}, <{i64}>}>, <{[2 x i64]}>, <4 x i64>}>, <{{<{i64, i64, i64, i1, float}>, <{float, i64}>}}>, {<{{i32, i64, i1, i8, i64}, {i32, i64, i1}, {i1, i64, i8}, <{i32, i8, i8, i8, float}>, {i32, i8, i1, float, i1}}>, <2 x i1>}}>, <5 x float>}> %v9, 0, 3, 0, 3, 1
    %v13 = extractvalue <{{[2 x i64]*, {<6 x float>, float*}, <{<5 x i1>, {i32, i1, i32}, <{i32, i8, i1, i8, i8}>, <{i64, i8}>, <{i1, i64}>}>, <{float*, [1 x i8]}>, <{<4 x i8>, i8*, <{i32, i64, i1, i64, float}>, <{i64, float, i32}>, {float, float, i64, i32}}>}*, {{<2 x i1>, {{i32, i64, i8}, [2 x i1], [1 x i32]}, <2 x float>}}}> %v5, 1, 0, 1
    br label %b14

b14:
    %v15 = mul i32 2, 4294967292
    %v16 = icmp ule i32 %v15, 2
    %v17 = select i1 %v16, i32 %v15, i32 2
    %v18 = icmp ugt i32 %v17, 0
    br i1 %v18, label %b23, label %b19

b23:
    %v24 = phi i32 [ %v17, %b14 ], [ %v25, %b22 ]
    %v27 = ptrtoint <6 x i1>* @g2 to i64
    %v28 = alloca i8
    store i8 %v12, i8* %v28, align 1
    ret i64 %v27

b22:
    %v25 = sub i32 %v24, 1
    %v26 = icmp ugt i32 %v25, 0
    br i1 %v26, label %b23, label %b19

b19:
    %v20 = getelementptr <5 x i1>, <5 x i1>* @g3, i32 0
    %v21 = udiv i8 %v12, 2
    ret i64 %v11
}


define  {i1, {[4 x {{i1, i8, i8, i1}, {i64, i8}, <{i32}>}]}} @g30(<{[3 x {<6 x i8>}]}> %v31, {[0 x <2 x i64>]} %v32, <4 x i1> %v33) {
b34:
    %v35 = insertelement <4 x i1> %v33, i1 0, i32 3
    br label %b36

b36:
    %v37 = sub i32 4294967295, 4
    %v38 = icmp ule i32 %v37, 7
    %v39 = select i1 %v38, i32 %v37, i32 7
    %v40 = icmp ugt i32 %v39, 0
    br i1 %v40, label %b49, label %b41

b49:
    %v50 = phi i32 [ %v39, %b36 ], [ %v51, %b48 ]
    %v53 = insertelement <4 x i1> %v35, i1 %v38, i32 0
    %v54 = insertvalue {[0 x <2 x i64>]} %v32, [0 x <2 x i64>] [], 0
    %v55 = getelementptr {i32, float, float, i64}, {i32, float, float, i64}* @g1, i32 0, i32 2
    ret {i1, {[4 x {{i1, i8, i8, i1}, {i64, i8}, <{i32}>}]}} {i1 0, {[4 x {{i1, i8, i8, i1}, {i64, i8}, <{i32}>}]} {[4 x {{i1, i8, i8, i1}, {i64, i8}, <{i32}>}] [{{i1, i8, i8, i1}, {i64, i8}, <{i32}>} {{i1, i8, i8, i1} {i1 0, i8 2, i8 253, i1 1}, {i64, i8} {i64 18446744073709551611, i8 5}, <{i32}> <{i32 4}>}, {{i1, i8, i8, i1}, {i64, i8}, <{i32}>} {{i1, i8, i8, i1} {i1 1, i8 3, i8 1, i1 1}, {i64, i8} {i64 4, i8 251}, <{i32}> <{i32 4294967293}>}, {{i1, i8, i8, i1}, {i64, i8}, <{i32}>} {{i1, i8, i8, i1} {i1 1, i8 252, i8 1, i1 0}, {i64, i8} {i64 1, i8 254}, <{i32}> <{i32 1}>}, {{i1, i8, i8, i1}, {i64, i8}, <{i32}>} {{i1, i8, i8, i1} {i1 0, i8 4, i8 251, i1 1}, {i64, i8} {i64 1, i8 5}, <{i32}> <{i32 0}>}]}}

b48:
    %v51 = sub i32 %v50, 1
    %v52 = icmp ugt i32 %v51, 0
    br i1 %v52, label %b49, label %b41

b41:
    %v42 = alloca <4 x i1>
    store <4 x i1> %v33, <4 x i1>* %v42, align 1
    store {i32, float, float, i64} {i32 4294967294, float 0x439346ac60000000, float 0x408a4fe220000000, i64 18446744073709551613}, {i32, float, float, i64}* @g1, align 1
    %v45 = insertelement <4 x i1> %v33, i1 %v38, i32 2
    %v46 = insertvalue {[0 x <2 x i64>]} %v32, [0 x <2 x i64>] [], 0
    %v47 = ptrtoint <6 x i1>* @g2 to i64
    ret {i1, {[4 x {{i1, i8, i8, i1}, {i64, i8}, <{i32}>}]}} {i1 1, {[4 x {{i1, i8, i8, i1}, {i64, i8}, <{i32}>}]} {[4 x {{i1, i8, i8, i1}, {i64, i8}, <{i32}>}] [{{i1, i8, i8, i1}, {i64, i8}, <{i32}>} {{i1, i8, i8, i1} {i1 1, i8 0, i8 255, i1 1}, {i64, i8} {i64 18446744073709551615, i8 252}, <{i32}> <{i32 4294967294}>}, {{i1, i8, i8, i1}, {i64, i8}, <{i32}>} {{i1, i8, i8, i1} {i1 1, i8 251, i8 252, i1 0}, {i64, i8} {i64 3, i8 251}, <{i32}> <{i32 4294967291}>}, {{i1, i8, i8, i1}, {i64, i8}, <{i32}>} {{i1, i8, i8, i1} {i1 1, i8 252, i8 252, i1 0}, {i64, i8} {i64 0, i8 5}, <{i32}> <{i32 3}>}, {{i1, i8, i8, i1}, {i64, i8}, <{i32}>} {{i1, i8, i8, i1} {i1 1, i8 254, i8 252, i1 1}, {i64, i8} {i64 18446744073709551615, i8 3}, <{i32}> <{i32 5}>}]}}
}


define  <4 x i64> @g56() {
b57:
    br label %b58

b58:
    %v59 = srem i32 4, -4
    %v60 = icmp ule i32 %v59, 10
    %v61 = select i1 %v60, i32 %v59, i32 10
    %v62 = icmp ugt i32 %v61, 0
    br i1 %v62, label %b69, label %b63

b69:
    %v70 = phi i32 [ %v61, %b58 ], [ %v71, %b68 ]
    %v73 = load <5 x i1>, <5 x i1>* @g3
    %v74 = or i1 %v60, %v60
    %v75 = getelementptr <{i8, <{<{<{<{float, float, i1}>}>, <{{i64, i32, i1, i64}, <{i64, i32}>, <2 x float>, <2 x i1>, <{i8, i32, i8}>}>, <{<{i1}>, <{i64, i1}>}>, {i32, float, float, i64}*, {{i1, i32, i32}, {i8}, <6 x i64>, <2 x float>}}>, <2 x i1>}>}>, <{i8, <{<{<{<{float, float, i1}>}>, <{{i64, i32, i1, i64}, <{i64, i32}>, <2 x float>, <2 x i1>, <{i8, i32, i8}>}>, <{<{i1}>, <{i64, i1}>}>, {i32, float, float, i64}*, {{i1, i32, i32}, {i8}, <6 x i64>, <2 x float>}}>, <2 x i1>}>}>* @g0, i32 0, i32 1, i32 0, i32 4, i32 2
    ret <4 x i64> <i64 18446744073709551613, i64 18446744073709551614, i64 18446744073709551615, i64 18446744073709551611>

b68:
    %v71 = sub i32 %v70, 1
    %v72 = icmp ugt i32 %v71, 0
    br i1 %v72, label %b69, label %b63

b63:
    %v64 = getelementptr {i32, float, float, i64}, {i32, float, float, i64}* @g1, i32 0, i32 2
    store float 0x381a84c400000000, float* %v64, align 1
    %v66 = ptrtoint <5 x i1>* @g3 to i64
    %v67 = load {i32, float, float, i64}, {i32, float, float, i64}* @g1
    ret <4 x i64> <i64 5, i64 2, i64 18446744073709551614, i64 3>
}


define  i8 @main() {
b76:
    %v77 = getelementptr <5 x i1>, <5 x i1>* @g3, i32 0
    %v78 = load <6 x i1>, <6 x i1>* @g2
    %v79 = sdiv i1 0, -1
    %v80 = extractelement <6 x i1> %v78, i32 0
    br label %b81

b81:
    %v82 = extractelement <6 x i1> %v78, i32 2
    %v83 = ashr i1 %v82, 0
    br i1 %v82, label %b84, label %b91

b84:
    %v85 = lshr i8 0, 2
    %v86 = alloca i8
    store i8 254, i8* %v86, align 1
    %v88 = ptrtoint <6 x i1>* @g2 to i64
    %v89 = sdiv i32 4, 2
    store <5 x i1> <i1 0, i1 1, i1 1, i1 1, i1 1>, <5 x i1>* @g3, align 1
    ret i8 %v85

b91:
    %v92 = getelementptr <5 x i1>, <5 x i1>* @g3, i32 0
    ret i8 5
}
