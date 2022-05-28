define void @foo() {
  br label %1
  br label %1
}

define void @bar(i1 %cnd) {
  br i1 %cnd, label %1, label %1
  br label %1
}
