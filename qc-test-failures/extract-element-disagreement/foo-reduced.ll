; ModuleID = 'bugpoint-reduced-simplified.bc'
source_filename = "foo.ll"
target triple = "x86_64-pc-linux-gnu"

@g0 = global <7 x i1> <i1 false, i1 false, i1 false, i1 true, i1 false, i1 true, i1 false>

declare i8* @malloc(i8)

declare void @free(i8*)

declare <5 x i8> @g1({ i8 }, { [1 x <7 x i8>], float, i32 }, { <5 x i1>, { <{ <4 x i1> }>, i8, i32, float, [2 x <3 x i32>] }, <{ i32, [6 x i8], [5 x <3 x i1>], { [2 x [0 x i8]], [5 x <7 x i8>], <6 x i32>, <{ <6 x i8>, { i32, [2 x i8], i8, float, { float, i1, i1, i8, i1, i1 } }, <{ [1 x float], <{ float, float, i8, i32 }>, [6 x i1], { float, i1, i32 }, <2 x i1>, [0 x i8] }>, <2 x i32>, <1 x i32>, <1 x i32> }>, <4 x i32> }, <{ <{ [6 x i32] }>, <5 x i1> }>, <5 x float> }>, <{ <4 x float>, [0 x <2 x i8>], i8 }>, <{ [3 x <1 x i1>], <{ <{ { <{ i32, i1, i8 }>, <7 x float>, [1 x i32], i32 }, i8, <{ [1 x i32] }>, <3 x i8>, i8, float }> }> }>, { <6 x i1>, { [2 x <7 x float>], { { i1, <7 x i8> }, <{ { i1, float, i1, float, i32 } }>, { [1 x i1], [4 x float], i8, <{ float, i32 }>, i1, [4 x float] } }, <{ <{ i32, <7 x i8>, <{ i8, i8 }>, { i32, i32, i1, i1 }, i8, <{ i1, float, i1 }> }> }>, [2 x <{ { i8 }, [3 x i8], { float, i8, float } }>], float, { <7 x i1>, [0 x [5 x float]], [1 x <{ i1, i32, i32, i8, i32, i1 }>] } }, i8, <{ <{ { <{ i8, i1 }>, { i8, float }, [3 x i32], <5 x i32>, { i32, i8, i8, float, i32, i1 } }, { <{ float, i32, i8, float, i8 }>, <{ i8 }> }, <6 x i1> }>, <2 x i32>, <7 x i32>, [2 x <{ [1 x i8], { float, i1, float, i1, i8, i1 }, [1 x i8], <6 x i1>, [1 x i8], i1 }>], <5 x i1>, { float, <{ <2 x float>, { i1, float, i8, i32, i8 }, { float, i1, i1, i1, i8, float } }>, [5 x <4 x i32>], <3 x i8>, { i1 }, [6 x i1] } }>, { { [0 x { i32, float, float, float, i8 }], [0 x <5 x i32>], <{ i1, <{ i1 }>, [5 x i8] }>, [6 x [5 x float]] }, { [6 x <{ i8, i32 }>], i32, { i8, [6 x i8], [5 x i32], [4 x i32], <3 x float> } }, <3 x i1>, <{ { <5 x i32>, [4 x i32], [0 x i32], <{ i8, float, i8 }> }, <{ <{ i32, i1, i8, i32, float }>, [6 x i32], [2 x i1], float, [0 x float] }>, i8, { { i8, float, i8, i8, float, i32 }, [3 x i1], { i8, i1, i8, i8, i32 }, float, <2 x float> } }>, { i1, <2 x i1>, [0 x [0 x float]] }, <6 x i1> }, <{ [2 x <{ <{ i32, i32, i32, i1 }>, [1 x i8] }>], { i1, float, <{ <{ i8, float, i1, float, i32 }>, i8, { i1, float }, <{ i8, i32, i8 }>, <2 x i1>, <{ i1, float, i32, i32, i8, i1 }> }>, <{ [3 x float], <4 x i1>, <{ i1, i1 }>, <1 x i1> }>, [3 x { float }] }, [2 x { { i8, float, i1 }, [5 x i8] }] }> } }, <{ i32, { [2 x <2 x float>], <3 x i8>, [6 x float], i1 }, [5 x { <2 x i32>, i1, { i1, i1, i8, <{ { i32 }, i8, { float, float, float, i8, i32 }, [2 x i1], <6 x i32>, i8 }>, { <{ i1, i1 }> }, <1 x i1> }, <{ <{ { i1 }, <{ float, float, i1 }>, [6 x i8], <{ i32, i32 }>, { i8, float, float, i1, i32, i8 }, <2 x i32> }>, i8, [1 x float], <{ i1, <{ i1, i32, i8 }>, <1 x i32>, <{ i1, i8 }>, <4 x i8>, { i8, float, i32, float, i1, float } }>, [0 x i32], [1 x { i1 }] }>, [3 x [5 x i8]] }] }>, <{ [4 x float], <4 x i1> }>)

declare [2 x <6 x i1>] @g2()

declare i8 @g3({ <3 x i1> }, [1 x { <7 x i32>, <5 x i32>, [4 x { i32, <{ <5 x i1>, i32, i32 }>, <7 x i32>, [2 x [5 x i1]], [3 x <{ i1 }>] }] }], <6 x i32>, { <{ float, i32, <1 x float> }>, [1 x [4 x float]], { i32, i1 }, <{ <{ <{ <1 x i32>, i1, <{ i32, float }>, <4 x i8> }>, <{ [2 x i32], [2 x i32], [4 x i8], <3 x float> }> }>, i8 }>, <7 x i8> })

declare <6 x float> @g4(float, [6 x [2 x <1 x i32>]], i1)

define i8 @main() {
b11:
  %v45 = getelementptr <7 x i1>, <7 x i1>* @g0, i32 0
  %v46 = load <7 x i1>, <7 x i1>* %v45, align 1
  %v47 = extractelement <7 x i1> %v46, i32 3
  %v49 = ashr i8 -2, 6
  %common.ret.op = select i1 %v47, i8 %v49, i8 -6
  ret i8 %common.ret.op
}
