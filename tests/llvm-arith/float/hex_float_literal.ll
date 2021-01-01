define float @main(i8 %argc, i8** %arcv) {
  ret float 0x42faa3d700000000
}

; ASSERT EQ: float 468655825485824. = call float @main(i64 0, i8** null)

