define i1000 @src(i1000 %x) {
    %r = add i1000 %x, 11
    ret i1000 %r
}

define i1000 @tgt(i1000 %x) {
    %r = sub i1000 %x, -11
    ret i1000 %r
}

; Disabled because we don't support i1000s
