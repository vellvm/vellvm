define double @main(i8 %argc, i8** %argv) {
  ret double 0x42faa3d700000000
}


define double @foo() {
  ret double 0x42faa3d700000000
}


define double @bar() {
  ret double 0x31
}


; ASSERT EQ: double 468655825485824. = call double @foo()
; ASSERT EQ: double 0x42faa3d700000000 = call double @foo()


; ASSERT EQ: double 0x31 = call double @bar()




