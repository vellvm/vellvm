@g0 = global <7 x i1> <i1 false, i1 false, i1 false, i1 true, i1 false, i1 true, i1 false>

define i8 @main() {
b11:
  %v46 = load <7 x i1>, <7 x i1>* @g0, align 1
  %v47 = extractelement <7 x i1> %v46, i32 2
  %v49 = ashr i8 -2, 6
  %common.ret.op = select i1 %v47, i8 %v49, i8 -6
  ret i8 %common.ret.op
}
