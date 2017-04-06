define void @foo() {
  ret void
}

define void @bar() {
  call void @foo()
  ret void
}

define void @baz() {
  %d = alloca void ()*
  store void ()* @foo, void ()** %d
  %f = load void ()*, void ()** %d
  call void %f ()
  ret void
}

%T = type {void ()*, i64}

define void @buz() {
  %x = alloca %T
  %p = getelementptr %T, %T* %x, i32 0, i32 0
  store void ()* @foo, void ()** %p
  %v = load %T, %T* %x
  %f = extractvalue %T %v, 0
  call void %f ()
  ret void
}
