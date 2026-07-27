; PERF: per-call function-pointer dispatch vs. module size.
; A module with 5000 trivial functions; a counted loop calls the
; last-defined one 40000 times. Function dispatch (lookup_defn in
; denote_mcfg) resolves the callee's address in an AVL IntMap built
; once in TopLevel, so per-call cost stays flat in the number of
; definitions; an association-list dispatch (as upstream) scans the
; definitions per call and makes this test blow up, as would
; rebuilding the map per call. Compare per-call cost against
; calls-fib.ll (many calls, two functions) and calls-large-fn.ll
; (per-call setup vs. callee size).
;
; Tune: regenerate with a different N / K (see perf/README.md).
; Result is K (the callee is the successor function).

define i64 @f0(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f5(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f6(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f7(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f8(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f9(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f10(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f11(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f12(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f13(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f14(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f15(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f16(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f17(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f18(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f19(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f20(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f21(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f22(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f23(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f24(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f25(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f26(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f27(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f28(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f29(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f30(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f31(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f32(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f33(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f34(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f35(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f36(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f37(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f38(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f39(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f40(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f41(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f42(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f43(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f44(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f45(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f46(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f47(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f48(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f49(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f50(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f51(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f52(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f53(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f54(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f55(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f56(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f57(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f58(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f59(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f60(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f61(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f62(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f63(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f64(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f65(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f66(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f67(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f68(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f69(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f70(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f71(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f72(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f73(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f74(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f75(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f76(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f77(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f78(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f79(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f80(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f81(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f82(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f83(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f84(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f85(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f86(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f87(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f88(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f89(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f90(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f91(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f92(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f93(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f94(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f95(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f96(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f97(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f98(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f99(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f100(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f101(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f102(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f103(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f104(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f105(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f106(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f107(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f108(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f109(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f110(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f111(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f112(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f113(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f114(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f115(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f116(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f117(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f118(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f119(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f120(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f121(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f122(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f123(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f124(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f125(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f126(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f127(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f128(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f129(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f130(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f131(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f132(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f133(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f134(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f135(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f136(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f137(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f138(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f139(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f140(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f141(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f142(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f143(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f144(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f145(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f146(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f147(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f148(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f149(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f150(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f151(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f152(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f153(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f154(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f155(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f156(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f157(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f158(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f159(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f160(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f161(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f162(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f163(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f164(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f165(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f166(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f167(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f168(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f169(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f170(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f171(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f172(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f173(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f174(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f175(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f176(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f177(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f178(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f179(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f180(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f181(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f182(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f183(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f184(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f185(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f186(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f187(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f188(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f189(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f190(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f191(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f192(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f193(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f194(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f195(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f196(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f197(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f198(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f199(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f200(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f201(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f202(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f203(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f204(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f205(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f206(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f207(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f208(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f209(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f210(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f211(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f212(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f213(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f214(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f215(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f216(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f217(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f218(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f219(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f220(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f221(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f222(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f223(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f224(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f225(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f226(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f227(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f228(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f229(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f230(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f231(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f232(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f233(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f234(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f235(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f236(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f237(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f238(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f239(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f240(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f241(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f242(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f243(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f244(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f245(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f246(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f247(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f248(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f249(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f250(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f251(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f252(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f253(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f254(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f255(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f256(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f257(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f258(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f259(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f260(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f261(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f262(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f263(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f264(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f265(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f266(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f267(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f268(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f269(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f270(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f271(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f272(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f273(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f274(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f275(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f276(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f277(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f278(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f279(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f280(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f281(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f282(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f283(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f284(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f285(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f286(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f287(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f288(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f289(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f290(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f291(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f292(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f293(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f294(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f295(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f296(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f297(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f298(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f299(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f300(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f301(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f302(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f303(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f304(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f305(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f306(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f307(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f308(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f309(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f310(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f311(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f312(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f313(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f314(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f315(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f316(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f317(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f318(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f319(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f320(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f321(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f322(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f323(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f324(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f325(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f326(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f327(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f328(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f329(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f330(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f331(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f332(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f333(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f334(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f335(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f336(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f337(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f338(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f339(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f340(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f341(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f342(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f343(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f344(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f345(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f346(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f347(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f348(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f349(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f350(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f351(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f352(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f353(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f354(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f355(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f356(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f357(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f358(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f359(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f360(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f361(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f362(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f363(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f364(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f365(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f366(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f367(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f368(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f369(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f370(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f371(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f372(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f373(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f374(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f375(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f376(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f377(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f378(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f379(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f380(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f381(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f382(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f383(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f384(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f385(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f386(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f387(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f388(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f389(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f390(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f391(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f392(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f393(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f394(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f395(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f396(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f397(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f398(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f399(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f400(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f401(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f402(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f403(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f404(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f405(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f406(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f407(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f408(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f409(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f410(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f411(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f412(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f413(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f414(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f415(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f416(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f417(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f418(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f419(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f420(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f421(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f422(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f423(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f424(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f425(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f426(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f427(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f428(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f429(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f430(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f431(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f432(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f433(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f434(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f435(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f436(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f437(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f438(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f439(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f440(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f441(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f442(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f443(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f444(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f445(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f446(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f447(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f448(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f449(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f450(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f451(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f452(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f453(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f454(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f455(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f456(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f457(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f458(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f459(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f460(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f461(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f462(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f463(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f464(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f465(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f466(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f467(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f468(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f469(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f470(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f471(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f472(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f473(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f474(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f475(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f476(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f477(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f478(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f479(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f480(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f481(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f482(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f483(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f484(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f485(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f486(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f487(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f488(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f489(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f490(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f491(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f492(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f493(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f494(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f495(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f496(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f497(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f498(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f499(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f500(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f501(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f502(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f503(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f504(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f505(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f506(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f507(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f508(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f509(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f510(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f511(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f512(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f513(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f514(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f515(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f516(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f517(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f518(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f519(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f520(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f521(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f522(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f523(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f524(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f525(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f526(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f527(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f528(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f529(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f530(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f531(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f532(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f533(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f534(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f535(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f536(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f537(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f538(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f539(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f540(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f541(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f542(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f543(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f544(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f545(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f546(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f547(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f548(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f549(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f550(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f551(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f552(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f553(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f554(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f555(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f556(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f557(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f558(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f559(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f560(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f561(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f562(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f563(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f564(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f565(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f566(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f567(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f568(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f569(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f570(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f571(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f572(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f573(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f574(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f575(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f576(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f577(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f578(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f579(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f580(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f581(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f582(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f583(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f584(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f585(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f586(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f587(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f588(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f589(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f590(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f591(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f592(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f593(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f594(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f595(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f596(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f597(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f598(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f599(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f600(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f601(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f602(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f603(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f604(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f605(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f606(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f607(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f608(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f609(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f610(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f611(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f612(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f613(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f614(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f615(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f616(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f617(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f618(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f619(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f620(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f621(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f622(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f623(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f624(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f625(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f626(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f627(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f628(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f629(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f630(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f631(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f632(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f633(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f634(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f635(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f636(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f637(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f638(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f639(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f640(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f641(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f642(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f643(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f644(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f645(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f646(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f647(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f648(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f649(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f650(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f651(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f652(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f653(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f654(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f655(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f656(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f657(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f658(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f659(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f660(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f661(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f662(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f663(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f664(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f665(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f666(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f667(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f668(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f669(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f670(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f671(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f672(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f673(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f674(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f675(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f676(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f677(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f678(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f679(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f680(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f681(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f682(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f683(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f684(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f685(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f686(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f687(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f688(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f689(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f690(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f691(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f692(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f693(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f694(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f695(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f696(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f697(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f698(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f699(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f700(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f701(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f702(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f703(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f704(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f705(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f706(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f707(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f708(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f709(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f710(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f711(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f712(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f713(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f714(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f715(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f716(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f717(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f718(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f719(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f720(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f721(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f722(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f723(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f724(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f725(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f726(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f727(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f728(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f729(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f730(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f731(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f732(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f733(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f734(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f735(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f736(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f737(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f738(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f739(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f740(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f741(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f742(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f743(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f744(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f745(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f746(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f747(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f748(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f749(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f750(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f751(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f752(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f753(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f754(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f755(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f756(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f757(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f758(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f759(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f760(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f761(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f762(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f763(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f764(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f765(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f766(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f767(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f768(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f769(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f770(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f771(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f772(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f773(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f774(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f775(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f776(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f777(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f778(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f779(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f780(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f781(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f782(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f783(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f784(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f785(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f786(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f787(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f788(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f789(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f790(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f791(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f792(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f793(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f794(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f795(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f796(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f797(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f798(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f799(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f800(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f801(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f802(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f803(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f804(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f805(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f806(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f807(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f808(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f809(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f810(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f811(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f812(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f813(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f814(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f815(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f816(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f817(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f818(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f819(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f820(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f821(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f822(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f823(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f824(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f825(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f826(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f827(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f828(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f829(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f830(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f831(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f832(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f833(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f834(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f835(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f836(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f837(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f838(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f839(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f840(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f841(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f842(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f843(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f844(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f845(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f846(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f847(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f848(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f849(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f850(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f851(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f852(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f853(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f854(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f855(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f856(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f857(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f858(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f859(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f860(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f861(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f862(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f863(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f864(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f865(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f866(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f867(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f868(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f869(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f870(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f871(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f872(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f873(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f874(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f875(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f876(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f877(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f878(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f879(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f880(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f881(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f882(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f883(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f884(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f885(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f886(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f887(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f888(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f889(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f890(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f891(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f892(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f893(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f894(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f895(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f896(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f897(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f898(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f899(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f900(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f901(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f902(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f903(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f904(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f905(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f906(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f907(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f908(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f909(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f910(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f911(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f912(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f913(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f914(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f915(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f916(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f917(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f918(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f919(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f920(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f921(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f922(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f923(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f924(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f925(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f926(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f927(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f928(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f929(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f930(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f931(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f932(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f933(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f934(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f935(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f936(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f937(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f938(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f939(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f940(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f941(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f942(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f943(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f944(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f945(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f946(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f947(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f948(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f949(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f950(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f951(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f952(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f953(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f954(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f955(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f956(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f957(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f958(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f959(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f960(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f961(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f962(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f963(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f964(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f965(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f966(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f967(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f968(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f969(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f970(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f971(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f972(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f973(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f974(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f975(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f976(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f977(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f978(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f979(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f980(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f981(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f982(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f983(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f984(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f985(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f986(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f987(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f988(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f989(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f990(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f991(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f992(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f993(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f994(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f995(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f996(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f997(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f998(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f999(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1000(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1001(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1002(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1003(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1004(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1005(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1006(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1007(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1008(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1009(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1010(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1011(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1012(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1013(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1014(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1015(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1016(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1017(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1018(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1019(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1020(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1021(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1022(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1023(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1024(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1025(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1026(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1027(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1028(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1029(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1030(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1031(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1032(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1033(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1034(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1035(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1036(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1037(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1038(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1039(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1040(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1041(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1042(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1043(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1044(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1045(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1046(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1047(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1048(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1049(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1050(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1051(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1052(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1053(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1054(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1055(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1056(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1057(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1058(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1059(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1060(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1061(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1062(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1063(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1064(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1065(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1066(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1067(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1068(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1069(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1070(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1071(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1072(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1073(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1074(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1075(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1076(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1077(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1078(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1079(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1080(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1081(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1082(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1083(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1084(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1085(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1086(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1087(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1088(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1089(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1090(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1091(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1092(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1093(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1094(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1095(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1096(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1097(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1098(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1099(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1100(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1101(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1102(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1103(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1104(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1105(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1106(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1107(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1108(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1109(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1110(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1111(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1112(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1113(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1114(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1115(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1116(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1117(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1118(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1119(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1120(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1121(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1122(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1123(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1124(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1125(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1126(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1127(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1128(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1129(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1130(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1131(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1132(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1133(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1134(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1135(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1136(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1137(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1138(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1139(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1140(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1141(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1142(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1143(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1144(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1145(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1146(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1147(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1148(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1149(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1150(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1151(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1152(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1153(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1154(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1155(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1156(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1157(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1158(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1159(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1160(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1161(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1162(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1163(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1164(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1165(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1166(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1167(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1168(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1169(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1170(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1171(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1172(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1173(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1174(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1175(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1176(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1177(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1178(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1179(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1180(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1181(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1182(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1183(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1184(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1185(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1186(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1187(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1188(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1189(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1190(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1191(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1192(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1193(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1194(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1195(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1196(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1197(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1198(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1199(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1200(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1201(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1202(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1203(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1204(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1205(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1206(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1207(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1208(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1209(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1210(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1211(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1212(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1213(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1214(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1215(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1216(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1217(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1218(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1219(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1220(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1221(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1222(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1223(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1224(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1225(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1226(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1227(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1228(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1229(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1230(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1231(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1232(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1233(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1234(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1235(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1236(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1237(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1238(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1239(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1240(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1241(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1242(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1243(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1244(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1245(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1246(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1247(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1248(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1249(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1250(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1251(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1252(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1253(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1254(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1255(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1256(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1257(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1258(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1259(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1260(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1261(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1262(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1263(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1264(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1265(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1266(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1267(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1268(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1269(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1270(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1271(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1272(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1273(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1274(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1275(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1276(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1277(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1278(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1279(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1280(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1281(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1282(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1283(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1284(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1285(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1286(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1287(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1288(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1289(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1290(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1291(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1292(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1293(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1294(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1295(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1296(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1297(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1298(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1299(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1300(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1301(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1302(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1303(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1304(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1305(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1306(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1307(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1308(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1309(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1310(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1311(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1312(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1313(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1314(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1315(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1316(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1317(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1318(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1319(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1320(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1321(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1322(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1323(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1324(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1325(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1326(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1327(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1328(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1329(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1330(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1331(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1332(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1333(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1334(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1335(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1336(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1337(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1338(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1339(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1340(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1341(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1342(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1343(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1344(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1345(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1346(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1347(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1348(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1349(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1350(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1351(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1352(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1353(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1354(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1355(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1356(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1357(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1358(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1359(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1360(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1361(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1362(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1363(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1364(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1365(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1366(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1367(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1368(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1369(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1370(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1371(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1372(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1373(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1374(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1375(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1376(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1377(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1378(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1379(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1380(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1381(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1382(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1383(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1384(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1385(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1386(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1387(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1388(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1389(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1390(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1391(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1392(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1393(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1394(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1395(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1396(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1397(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1398(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1399(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1400(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1401(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1402(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1403(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1404(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1405(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1406(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1407(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1408(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1409(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1410(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1411(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1412(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1413(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1414(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1415(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1416(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1417(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1418(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1419(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1420(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1421(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1422(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1423(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1424(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1425(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1426(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1427(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1428(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1429(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1430(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1431(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1432(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1433(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1434(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1435(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1436(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1437(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1438(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1439(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1440(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1441(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1442(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1443(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1444(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1445(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1446(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1447(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1448(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1449(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1450(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1451(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1452(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1453(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1454(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1455(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1456(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1457(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1458(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1459(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1460(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1461(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1462(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1463(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1464(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1465(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1466(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1467(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1468(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1469(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1470(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1471(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1472(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1473(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1474(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1475(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1476(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1477(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1478(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1479(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1480(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1481(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1482(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1483(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1484(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1485(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1486(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1487(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1488(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1489(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1490(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1491(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1492(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1493(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1494(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1495(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1496(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1497(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1498(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1499(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1500(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1501(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1502(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1503(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1504(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1505(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1506(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1507(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1508(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1509(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1510(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1511(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1512(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1513(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1514(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1515(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1516(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1517(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1518(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1519(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1520(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1521(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1522(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1523(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1524(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1525(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1526(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1527(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1528(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1529(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1530(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1531(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1532(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1533(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1534(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1535(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1536(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1537(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1538(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1539(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1540(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1541(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1542(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1543(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1544(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1545(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1546(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1547(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1548(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1549(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1550(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1551(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1552(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1553(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1554(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1555(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1556(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1557(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1558(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1559(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1560(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1561(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1562(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1563(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1564(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1565(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1566(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1567(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1568(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1569(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1570(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1571(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1572(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1573(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1574(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1575(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1576(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1577(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1578(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1579(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1580(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1581(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1582(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1583(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1584(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1585(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1586(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1587(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1588(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1589(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1590(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1591(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1592(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1593(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1594(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1595(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1596(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1597(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1598(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1599(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1600(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1601(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1602(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1603(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1604(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1605(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1606(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1607(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1608(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1609(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1610(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1611(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1612(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1613(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1614(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1615(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1616(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1617(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1618(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1619(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1620(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1621(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1622(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1623(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1624(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1625(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1626(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1627(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1628(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1629(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1630(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1631(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1632(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1633(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1634(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1635(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1636(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1637(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1638(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1639(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1640(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1641(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1642(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1643(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1644(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1645(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1646(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1647(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1648(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1649(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1650(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1651(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1652(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1653(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1654(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1655(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1656(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1657(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1658(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1659(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1660(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1661(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1662(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1663(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1664(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1665(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1666(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1667(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1668(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1669(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1670(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1671(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1672(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1673(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1674(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1675(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1676(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1677(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1678(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1679(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1680(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1681(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1682(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1683(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1684(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1685(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1686(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1687(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1688(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1689(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1690(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1691(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1692(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1693(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1694(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1695(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1696(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1697(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1698(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1699(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1700(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1701(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1702(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1703(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1704(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1705(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1706(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1707(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1708(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1709(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1710(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1711(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1712(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1713(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1714(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1715(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1716(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1717(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1718(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1719(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1720(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1721(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1722(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1723(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1724(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1725(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1726(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1727(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1728(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1729(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1730(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1731(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1732(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1733(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1734(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1735(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1736(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1737(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1738(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1739(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1740(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1741(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1742(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1743(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1744(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1745(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1746(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1747(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1748(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1749(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1750(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1751(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1752(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1753(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1754(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1755(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1756(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1757(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1758(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1759(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1760(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1761(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1762(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1763(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1764(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1765(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1766(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1767(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1768(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1769(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1770(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1771(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1772(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1773(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1774(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1775(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1776(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1777(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1778(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1779(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1780(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1781(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1782(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1783(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1784(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1785(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1786(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1787(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1788(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1789(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1790(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1791(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1792(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1793(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1794(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1795(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1796(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1797(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1798(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1799(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1800(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1801(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1802(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1803(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1804(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1805(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1806(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1807(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1808(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1809(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1810(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1811(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1812(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1813(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1814(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1815(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1816(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1817(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1818(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1819(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1820(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1821(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1822(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1823(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1824(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1825(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1826(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1827(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1828(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1829(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1830(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1831(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1832(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1833(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1834(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1835(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1836(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1837(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1838(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1839(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1840(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1841(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1842(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1843(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1844(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1845(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1846(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1847(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1848(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1849(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1850(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1851(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1852(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1853(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1854(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1855(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1856(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1857(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1858(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1859(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1860(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1861(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1862(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1863(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1864(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1865(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1866(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1867(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1868(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1869(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1870(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1871(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1872(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1873(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1874(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1875(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1876(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1877(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1878(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1879(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1880(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1881(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1882(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1883(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1884(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1885(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1886(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1887(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1888(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1889(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1890(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1891(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1892(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1893(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1894(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1895(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1896(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1897(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1898(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1899(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1900(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1901(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1902(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1903(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1904(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1905(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1906(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1907(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1908(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1909(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1910(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1911(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1912(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1913(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1914(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1915(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1916(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1917(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1918(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1919(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1920(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1921(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1922(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1923(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1924(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1925(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1926(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1927(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1928(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1929(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1930(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1931(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1932(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1933(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1934(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1935(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1936(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1937(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1938(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1939(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1940(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1941(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1942(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1943(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1944(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1945(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1946(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1947(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1948(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1949(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1950(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1951(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1952(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1953(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1954(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1955(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1956(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1957(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1958(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1959(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1960(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1961(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1962(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1963(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1964(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1965(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1966(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1967(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1968(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1969(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1970(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1971(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1972(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1973(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1974(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1975(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1976(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1977(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1978(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1979(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1980(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1981(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1982(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1983(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1984(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1985(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1986(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1987(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1988(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1989(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1990(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1991(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1992(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1993(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1994(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1995(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1996(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1997(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1998(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f1999(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2000(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2001(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2002(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2003(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2004(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2005(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2006(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2007(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2008(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2009(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2010(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2011(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2012(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2013(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2014(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2015(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2016(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2017(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2018(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2019(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2020(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2021(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2022(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2023(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2024(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2025(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2026(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2027(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2028(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2029(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2030(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2031(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2032(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2033(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2034(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2035(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2036(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2037(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2038(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2039(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2040(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2041(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2042(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2043(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2044(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2045(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2046(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2047(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2048(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2049(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2050(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2051(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2052(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2053(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2054(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2055(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2056(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2057(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2058(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2059(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2060(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2061(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2062(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2063(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2064(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2065(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2066(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2067(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2068(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2069(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2070(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2071(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2072(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2073(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2074(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2075(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2076(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2077(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2078(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2079(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2080(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2081(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2082(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2083(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2084(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2085(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2086(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2087(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2088(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2089(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2090(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2091(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2092(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2093(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2094(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2095(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2096(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2097(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2098(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2099(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2100(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2101(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2102(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2103(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2104(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2105(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2106(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2107(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2108(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2109(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2110(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2111(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2112(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2113(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2114(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2115(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2116(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2117(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2118(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2119(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2120(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2121(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2122(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2123(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2124(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2125(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2126(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2127(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2128(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2129(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2130(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2131(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2132(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2133(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2134(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2135(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2136(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2137(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2138(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2139(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2140(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2141(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2142(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2143(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2144(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2145(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2146(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2147(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2148(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2149(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2150(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2151(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2152(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2153(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2154(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2155(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2156(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2157(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2158(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2159(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2160(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2161(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2162(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2163(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2164(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2165(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2166(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2167(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2168(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2169(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2170(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2171(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2172(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2173(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2174(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2175(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2176(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2177(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2178(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2179(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2180(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2181(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2182(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2183(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2184(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2185(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2186(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2187(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2188(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2189(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2190(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2191(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2192(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2193(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2194(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2195(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2196(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2197(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2198(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2199(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2200(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2201(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2202(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2203(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2204(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2205(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2206(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2207(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2208(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2209(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2210(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2211(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2212(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2213(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2214(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2215(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2216(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2217(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2218(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2219(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2220(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2221(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2222(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2223(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2224(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2225(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2226(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2227(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2228(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2229(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2230(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2231(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2232(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2233(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2234(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2235(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2236(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2237(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2238(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2239(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2240(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2241(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2242(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2243(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2244(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2245(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2246(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2247(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2248(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2249(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2250(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2251(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2252(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2253(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2254(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2255(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2256(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2257(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2258(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2259(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2260(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2261(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2262(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2263(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2264(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2265(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2266(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2267(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2268(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2269(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2270(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2271(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2272(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2273(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2274(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2275(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2276(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2277(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2278(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2279(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2280(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2281(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2282(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2283(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2284(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2285(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2286(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2287(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2288(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2289(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2290(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2291(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2292(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2293(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2294(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2295(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2296(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2297(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2298(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2299(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2300(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2301(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2302(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2303(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2304(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2305(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2306(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2307(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2308(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2309(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2310(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2311(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2312(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2313(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2314(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2315(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2316(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2317(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2318(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2319(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2320(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2321(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2322(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2323(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2324(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2325(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2326(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2327(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2328(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2329(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2330(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2331(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2332(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2333(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2334(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2335(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2336(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2337(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2338(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2339(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2340(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2341(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2342(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2343(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2344(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2345(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2346(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2347(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2348(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2349(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2350(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2351(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2352(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2353(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2354(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2355(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2356(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2357(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2358(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2359(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2360(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2361(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2362(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2363(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2364(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2365(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2366(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2367(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2368(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2369(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2370(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2371(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2372(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2373(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2374(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2375(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2376(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2377(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2378(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2379(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2380(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2381(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2382(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2383(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2384(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2385(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2386(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2387(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2388(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2389(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2390(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2391(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2392(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2393(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2394(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2395(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2396(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2397(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2398(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2399(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2400(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2401(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2402(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2403(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2404(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2405(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2406(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2407(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2408(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2409(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2410(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2411(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2412(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2413(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2414(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2415(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2416(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2417(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2418(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2419(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2420(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2421(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2422(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2423(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2424(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2425(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2426(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2427(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2428(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2429(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2430(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2431(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2432(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2433(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2434(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2435(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2436(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2437(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2438(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2439(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2440(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2441(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2442(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2443(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2444(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2445(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2446(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2447(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2448(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2449(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2450(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2451(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2452(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2453(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2454(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2455(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2456(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2457(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2458(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2459(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2460(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2461(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2462(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2463(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2464(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2465(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2466(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2467(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2468(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2469(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2470(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2471(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2472(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2473(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2474(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2475(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2476(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2477(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2478(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2479(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2480(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2481(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2482(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2483(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2484(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2485(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2486(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2487(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2488(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2489(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2490(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2491(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2492(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2493(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2494(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2495(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2496(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2497(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2498(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2499(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2500(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2501(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2502(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2503(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2504(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2505(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2506(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2507(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2508(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2509(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2510(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2511(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2512(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2513(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2514(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2515(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2516(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2517(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2518(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2519(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2520(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2521(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2522(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2523(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2524(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2525(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2526(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2527(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2528(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2529(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2530(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2531(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2532(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2533(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2534(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2535(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2536(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2537(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2538(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2539(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2540(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2541(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2542(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2543(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2544(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2545(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2546(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2547(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2548(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2549(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2550(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2551(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2552(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2553(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2554(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2555(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2556(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2557(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2558(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2559(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2560(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2561(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2562(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2563(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2564(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2565(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2566(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2567(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2568(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2569(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2570(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2571(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2572(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2573(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2574(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2575(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2576(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2577(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2578(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2579(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2580(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2581(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2582(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2583(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2584(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2585(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2586(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2587(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2588(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2589(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2590(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2591(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2592(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2593(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2594(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2595(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2596(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2597(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2598(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2599(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2600(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2601(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2602(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2603(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2604(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2605(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2606(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2607(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2608(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2609(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2610(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2611(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2612(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2613(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2614(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2615(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2616(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2617(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2618(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2619(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2620(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2621(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2622(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2623(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2624(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2625(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2626(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2627(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2628(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2629(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2630(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2631(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2632(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2633(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2634(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2635(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2636(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2637(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2638(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2639(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2640(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2641(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2642(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2643(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2644(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2645(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2646(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2647(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2648(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2649(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2650(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2651(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2652(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2653(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2654(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2655(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2656(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2657(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2658(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2659(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2660(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2661(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2662(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2663(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2664(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2665(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2666(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2667(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2668(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2669(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2670(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2671(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2672(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2673(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2674(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2675(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2676(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2677(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2678(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2679(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2680(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2681(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2682(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2683(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2684(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2685(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2686(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2687(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2688(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2689(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2690(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2691(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2692(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2693(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2694(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2695(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2696(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2697(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2698(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2699(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2700(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2701(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2702(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2703(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2704(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2705(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2706(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2707(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2708(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2709(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2710(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2711(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2712(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2713(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2714(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2715(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2716(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2717(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2718(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2719(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2720(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2721(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2722(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2723(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2724(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2725(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2726(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2727(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2728(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2729(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2730(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2731(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2732(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2733(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2734(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2735(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2736(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2737(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2738(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2739(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2740(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2741(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2742(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2743(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2744(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2745(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2746(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2747(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2748(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2749(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2750(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2751(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2752(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2753(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2754(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2755(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2756(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2757(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2758(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2759(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2760(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2761(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2762(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2763(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2764(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2765(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2766(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2767(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2768(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2769(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2770(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2771(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2772(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2773(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2774(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2775(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2776(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2777(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2778(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2779(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2780(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2781(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2782(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2783(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2784(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2785(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2786(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2787(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2788(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2789(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2790(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2791(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2792(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2793(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2794(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2795(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2796(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2797(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2798(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2799(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2800(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2801(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2802(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2803(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2804(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2805(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2806(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2807(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2808(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2809(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2810(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2811(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2812(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2813(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2814(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2815(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2816(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2817(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2818(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2819(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2820(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2821(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2822(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2823(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2824(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2825(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2826(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2827(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2828(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2829(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2830(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2831(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2832(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2833(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2834(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2835(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2836(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2837(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2838(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2839(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2840(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2841(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2842(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2843(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2844(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2845(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2846(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2847(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2848(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2849(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2850(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2851(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2852(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2853(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2854(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2855(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2856(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2857(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2858(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2859(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2860(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2861(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2862(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2863(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2864(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2865(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2866(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2867(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2868(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2869(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2870(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2871(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2872(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2873(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2874(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2875(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2876(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2877(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2878(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2879(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2880(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2881(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2882(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2883(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2884(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2885(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2886(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2887(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2888(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2889(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2890(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2891(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2892(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2893(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2894(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2895(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2896(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2897(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2898(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2899(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2900(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2901(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2902(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2903(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2904(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2905(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2906(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2907(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2908(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2909(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2910(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2911(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2912(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2913(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2914(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2915(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2916(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2917(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2918(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2919(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2920(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2921(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2922(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2923(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2924(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2925(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2926(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2927(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2928(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2929(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2930(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2931(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2932(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2933(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2934(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2935(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2936(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2937(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2938(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2939(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2940(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2941(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2942(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2943(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2944(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2945(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2946(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2947(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2948(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2949(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2950(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2951(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2952(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2953(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2954(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2955(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2956(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2957(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2958(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2959(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2960(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2961(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2962(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2963(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2964(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2965(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2966(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2967(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2968(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2969(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2970(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2971(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2972(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2973(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2974(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2975(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2976(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2977(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2978(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2979(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2980(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2981(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2982(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2983(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2984(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2985(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2986(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2987(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2988(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2989(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2990(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2991(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2992(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2993(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2994(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2995(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2996(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2997(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2998(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f2999(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3000(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3001(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3002(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3003(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3004(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3005(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3006(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3007(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3008(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3009(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3010(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3011(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3012(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3013(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3014(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3015(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3016(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3017(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3018(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3019(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3020(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3021(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3022(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3023(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3024(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3025(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3026(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3027(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3028(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3029(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3030(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3031(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3032(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3033(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3034(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3035(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3036(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3037(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3038(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3039(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3040(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3041(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3042(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3043(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3044(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3045(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3046(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3047(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3048(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3049(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3050(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3051(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3052(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3053(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3054(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3055(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3056(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3057(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3058(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3059(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3060(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3061(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3062(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3063(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3064(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3065(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3066(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3067(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3068(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3069(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3070(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3071(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3072(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3073(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3074(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3075(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3076(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3077(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3078(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3079(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3080(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3081(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3082(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3083(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3084(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3085(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3086(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3087(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3088(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3089(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3090(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3091(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3092(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3093(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3094(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3095(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3096(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3097(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3098(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3099(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3100(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3101(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3102(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3103(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3104(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3105(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3106(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3107(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3108(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3109(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3110(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3111(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3112(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3113(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3114(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3115(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3116(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3117(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3118(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3119(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3120(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3121(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3122(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3123(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3124(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3125(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3126(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3127(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3128(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3129(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3130(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3131(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3132(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3133(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3134(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3135(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3136(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3137(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3138(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3139(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3140(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3141(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3142(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3143(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3144(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3145(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3146(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3147(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3148(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3149(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3150(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3151(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3152(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3153(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3154(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3155(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3156(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3157(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3158(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3159(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3160(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3161(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3162(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3163(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3164(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3165(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3166(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3167(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3168(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3169(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3170(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3171(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3172(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3173(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3174(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3175(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3176(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3177(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3178(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3179(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3180(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3181(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3182(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3183(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3184(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3185(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3186(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3187(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3188(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3189(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3190(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3191(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3192(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3193(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3194(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3195(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3196(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3197(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3198(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3199(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3200(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3201(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3202(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3203(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3204(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3205(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3206(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3207(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3208(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3209(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3210(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3211(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3212(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3213(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3214(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3215(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3216(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3217(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3218(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3219(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3220(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3221(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3222(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3223(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3224(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3225(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3226(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3227(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3228(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3229(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3230(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3231(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3232(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3233(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3234(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3235(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3236(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3237(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3238(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3239(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3240(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3241(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3242(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3243(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3244(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3245(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3246(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3247(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3248(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3249(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3250(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3251(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3252(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3253(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3254(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3255(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3256(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3257(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3258(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3259(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3260(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3261(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3262(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3263(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3264(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3265(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3266(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3267(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3268(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3269(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3270(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3271(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3272(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3273(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3274(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3275(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3276(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3277(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3278(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3279(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3280(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3281(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3282(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3283(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3284(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3285(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3286(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3287(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3288(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3289(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3290(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3291(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3292(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3293(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3294(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3295(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3296(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3297(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3298(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3299(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3300(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3301(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3302(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3303(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3304(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3305(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3306(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3307(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3308(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3309(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3310(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3311(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3312(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3313(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3314(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3315(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3316(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3317(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3318(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3319(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3320(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3321(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3322(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3323(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3324(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3325(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3326(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3327(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3328(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3329(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3330(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3331(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3332(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3333(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3334(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3335(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3336(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3337(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3338(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3339(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3340(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3341(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3342(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3343(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3344(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3345(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3346(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3347(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3348(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3349(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3350(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3351(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3352(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3353(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3354(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3355(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3356(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3357(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3358(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3359(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3360(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3361(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3362(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3363(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3364(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3365(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3366(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3367(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3368(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3369(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3370(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3371(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3372(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3373(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3374(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3375(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3376(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3377(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3378(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3379(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3380(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3381(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3382(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3383(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3384(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3385(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3386(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3387(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3388(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3389(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3390(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3391(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3392(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3393(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3394(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3395(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3396(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3397(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3398(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3399(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3400(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3401(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3402(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3403(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3404(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3405(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3406(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3407(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3408(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3409(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3410(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3411(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3412(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3413(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3414(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3415(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3416(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3417(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3418(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3419(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3420(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3421(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3422(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3423(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3424(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3425(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3426(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3427(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3428(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3429(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3430(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3431(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3432(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3433(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3434(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3435(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3436(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3437(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3438(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3439(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3440(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3441(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3442(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3443(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3444(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3445(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3446(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3447(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3448(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3449(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3450(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3451(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3452(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3453(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3454(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3455(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3456(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3457(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3458(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3459(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3460(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3461(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3462(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3463(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3464(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3465(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3466(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3467(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3468(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3469(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3470(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3471(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3472(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3473(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3474(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3475(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3476(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3477(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3478(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3479(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3480(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3481(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3482(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3483(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3484(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3485(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3486(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3487(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3488(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3489(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3490(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3491(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3492(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3493(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3494(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3495(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3496(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3497(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3498(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3499(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3500(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3501(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3502(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3503(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3504(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3505(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3506(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3507(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3508(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3509(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3510(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3511(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3512(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3513(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3514(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3515(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3516(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3517(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3518(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3519(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3520(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3521(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3522(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3523(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3524(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3525(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3526(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3527(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3528(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3529(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3530(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3531(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3532(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3533(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3534(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3535(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3536(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3537(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3538(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3539(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3540(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3541(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3542(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3543(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3544(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3545(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3546(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3547(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3548(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3549(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3550(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3551(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3552(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3553(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3554(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3555(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3556(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3557(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3558(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3559(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3560(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3561(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3562(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3563(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3564(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3565(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3566(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3567(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3568(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3569(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3570(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3571(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3572(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3573(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3574(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3575(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3576(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3577(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3578(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3579(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3580(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3581(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3582(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3583(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3584(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3585(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3586(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3587(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3588(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3589(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3590(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3591(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3592(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3593(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3594(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3595(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3596(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3597(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3598(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3599(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3600(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3601(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3602(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3603(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3604(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3605(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3606(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3607(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3608(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3609(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3610(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3611(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3612(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3613(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3614(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3615(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3616(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3617(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3618(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3619(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3620(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3621(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3622(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3623(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3624(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3625(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3626(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3627(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3628(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3629(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3630(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3631(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3632(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3633(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3634(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3635(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3636(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3637(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3638(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3639(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3640(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3641(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3642(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3643(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3644(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3645(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3646(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3647(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3648(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3649(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3650(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3651(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3652(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3653(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3654(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3655(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3656(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3657(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3658(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3659(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3660(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3661(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3662(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3663(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3664(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3665(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3666(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3667(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3668(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3669(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3670(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3671(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3672(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3673(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3674(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3675(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3676(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3677(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3678(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3679(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3680(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3681(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3682(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3683(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3684(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3685(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3686(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3687(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3688(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3689(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3690(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3691(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3692(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3693(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3694(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3695(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3696(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3697(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3698(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3699(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3700(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3701(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3702(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3703(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3704(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3705(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3706(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3707(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3708(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3709(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3710(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3711(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3712(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3713(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3714(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3715(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3716(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3717(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3718(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3719(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3720(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3721(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3722(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3723(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3724(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3725(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3726(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3727(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3728(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3729(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3730(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3731(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3732(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3733(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3734(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3735(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3736(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3737(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3738(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3739(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3740(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3741(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3742(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3743(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3744(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3745(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3746(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3747(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3748(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3749(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3750(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3751(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3752(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3753(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3754(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3755(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3756(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3757(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3758(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3759(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3760(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3761(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3762(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3763(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3764(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3765(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3766(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3767(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3768(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3769(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3770(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3771(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3772(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3773(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3774(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3775(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3776(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3777(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3778(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3779(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3780(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3781(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3782(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3783(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3784(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3785(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3786(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3787(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3788(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3789(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3790(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3791(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3792(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3793(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3794(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3795(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3796(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3797(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3798(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3799(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3800(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3801(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3802(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3803(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3804(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3805(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3806(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3807(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3808(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3809(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3810(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3811(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3812(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3813(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3814(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3815(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3816(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3817(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3818(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3819(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3820(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3821(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3822(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3823(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3824(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3825(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3826(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3827(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3828(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3829(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3830(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3831(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3832(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3833(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3834(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3835(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3836(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3837(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3838(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3839(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3840(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3841(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3842(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3843(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3844(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3845(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3846(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3847(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3848(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3849(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3850(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3851(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3852(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3853(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3854(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3855(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3856(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3857(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3858(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3859(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3860(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3861(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3862(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3863(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3864(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3865(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3866(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3867(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3868(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3869(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3870(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3871(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3872(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3873(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3874(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3875(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3876(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3877(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3878(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3879(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3880(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3881(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3882(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3883(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3884(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3885(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3886(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3887(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3888(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3889(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3890(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3891(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3892(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3893(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3894(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3895(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3896(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3897(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3898(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3899(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3900(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3901(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3902(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3903(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3904(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3905(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3906(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3907(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3908(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3909(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3910(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3911(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3912(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3913(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3914(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3915(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3916(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3917(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3918(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3919(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3920(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3921(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3922(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3923(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3924(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3925(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3926(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3927(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3928(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3929(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3930(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3931(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3932(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3933(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3934(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3935(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3936(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3937(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3938(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3939(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3940(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3941(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3942(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3943(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3944(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3945(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3946(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3947(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3948(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3949(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3950(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3951(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3952(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3953(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3954(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3955(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3956(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3957(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3958(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3959(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3960(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3961(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3962(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3963(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3964(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3965(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3966(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3967(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3968(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3969(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3970(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3971(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3972(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3973(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3974(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3975(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3976(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3977(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3978(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3979(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3980(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3981(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3982(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3983(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3984(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3985(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3986(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3987(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3988(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3989(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3990(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3991(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3992(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3993(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3994(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3995(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3996(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3997(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3998(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f3999(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4000(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4001(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4002(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4003(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4004(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4005(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4006(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4007(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4008(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4009(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4010(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4011(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4012(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4013(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4014(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4015(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4016(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4017(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4018(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4019(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4020(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4021(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4022(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4023(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4024(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4025(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4026(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4027(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4028(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4029(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4030(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4031(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4032(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4033(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4034(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4035(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4036(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4037(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4038(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4039(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4040(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4041(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4042(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4043(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4044(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4045(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4046(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4047(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4048(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4049(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4050(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4051(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4052(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4053(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4054(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4055(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4056(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4057(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4058(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4059(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4060(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4061(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4062(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4063(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4064(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4065(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4066(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4067(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4068(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4069(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4070(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4071(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4072(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4073(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4074(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4075(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4076(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4077(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4078(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4079(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4080(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4081(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4082(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4083(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4084(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4085(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4086(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4087(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4088(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4089(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4090(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4091(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4092(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4093(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4094(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4095(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4096(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4097(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4098(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4099(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4100(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4101(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4102(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4103(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4104(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4105(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4106(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4107(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4108(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4109(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4110(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4111(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4112(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4113(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4114(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4115(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4116(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4117(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4118(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4119(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4120(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4121(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4122(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4123(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4124(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4125(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4126(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4127(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4128(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4129(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4130(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4131(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4132(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4133(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4134(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4135(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4136(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4137(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4138(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4139(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4140(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4141(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4142(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4143(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4144(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4145(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4146(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4147(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4148(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4149(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4150(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4151(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4152(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4153(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4154(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4155(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4156(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4157(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4158(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4159(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4160(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4161(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4162(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4163(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4164(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4165(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4166(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4167(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4168(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4169(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4170(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4171(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4172(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4173(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4174(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4175(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4176(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4177(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4178(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4179(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4180(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4181(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4182(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4183(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4184(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4185(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4186(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4187(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4188(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4189(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4190(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4191(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4192(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4193(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4194(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4195(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4196(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4197(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4198(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4199(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4200(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4201(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4202(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4203(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4204(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4205(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4206(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4207(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4208(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4209(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4210(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4211(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4212(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4213(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4214(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4215(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4216(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4217(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4218(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4219(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4220(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4221(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4222(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4223(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4224(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4225(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4226(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4227(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4228(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4229(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4230(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4231(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4232(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4233(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4234(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4235(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4236(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4237(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4238(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4239(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4240(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4241(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4242(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4243(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4244(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4245(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4246(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4247(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4248(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4249(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4250(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4251(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4252(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4253(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4254(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4255(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4256(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4257(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4258(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4259(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4260(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4261(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4262(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4263(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4264(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4265(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4266(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4267(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4268(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4269(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4270(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4271(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4272(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4273(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4274(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4275(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4276(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4277(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4278(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4279(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4280(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4281(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4282(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4283(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4284(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4285(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4286(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4287(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4288(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4289(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4290(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4291(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4292(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4293(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4294(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4295(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4296(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4297(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4298(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4299(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4300(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4301(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4302(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4303(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4304(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4305(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4306(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4307(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4308(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4309(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4310(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4311(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4312(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4313(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4314(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4315(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4316(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4317(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4318(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4319(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4320(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4321(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4322(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4323(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4324(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4325(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4326(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4327(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4328(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4329(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4330(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4331(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4332(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4333(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4334(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4335(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4336(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4337(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4338(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4339(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4340(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4341(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4342(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4343(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4344(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4345(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4346(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4347(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4348(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4349(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4350(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4351(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4352(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4353(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4354(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4355(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4356(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4357(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4358(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4359(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4360(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4361(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4362(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4363(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4364(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4365(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4366(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4367(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4368(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4369(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4370(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4371(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4372(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4373(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4374(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4375(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4376(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4377(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4378(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4379(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4380(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4381(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4382(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4383(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4384(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4385(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4386(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4387(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4388(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4389(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4390(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4391(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4392(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4393(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4394(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4395(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4396(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4397(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4398(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4399(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4400(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4401(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4402(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4403(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4404(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4405(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4406(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4407(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4408(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4409(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4410(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4411(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4412(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4413(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4414(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4415(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4416(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4417(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4418(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4419(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4420(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4421(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4422(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4423(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4424(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4425(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4426(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4427(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4428(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4429(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4430(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4431(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4432(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4433(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4434(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4435(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4436(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4437(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4438(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4439(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4440(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4441(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4442(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4443(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4444(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4445(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4446(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4447(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4448(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4449(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4450(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4451(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4452(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4453(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4454(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4455(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4456(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4457(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4458(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4459(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4460(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4461(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4462(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4463(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4464(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4465(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4466(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4467(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4468(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4469(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4470(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4471(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4472(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4473(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4474(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4475(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4476(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4477(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4478(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4479(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4480(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4481(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4482(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4483(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4484(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4485(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4486(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4487(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4488(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4489(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4490(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4491(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4492(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4493(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4494(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4495(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4496(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4497(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4498(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4499(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4500(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4501(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4502(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4503(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4504(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4505(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4506(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4507(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4508(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4509(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4510(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4511(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4512(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4513(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4514(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4515(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4516(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4517(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4518(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4519(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4520(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4521(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4522(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4523(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4524(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4525(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4526(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4527(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4528(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4529(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4530(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4531(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4532(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4533(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4534(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4535(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4536(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4537(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4538(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4539(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4540(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4541(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4542(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4543(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4544(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4545(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4546(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4547(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4548(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4549(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4550(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4551(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4552(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4553(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4554(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4555(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4556(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4557(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4558(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4559(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4560(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4561(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4562(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4563(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4564(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4565(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4566(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4567(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4568(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4569(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4570(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4571(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4572(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4573(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4574(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4575(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4576(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4577(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4578(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4579(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4580(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4581(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4582(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4583(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4584(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4585(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4586(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4587(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4588(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4589(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4590(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4591(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4592(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4593(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4594(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4595(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4596(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4597(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4598(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4599(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4600(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4601(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4602(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4603(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4604(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4605(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4606(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4607(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4608(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4609(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4610(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4611(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4612(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4613(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4614(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4615(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4616(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4617(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4618(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4619(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4620(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4621(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4622(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4623(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4624(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4625(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4626(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4627(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4628(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4629(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4630(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4631(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4632(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4633(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4634(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4635(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4636(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4637(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4638(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4639(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4640(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4641(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4642(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4643(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4644(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4645(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4646(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4647(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4648(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4649(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4650(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4651(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4652(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4653(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4654(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4655(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4656(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4657(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4658(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4659(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4660(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4661(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4662(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4663(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4664(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4665(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4666(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4667(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4668(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4669(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4670(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4671(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4672(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4673(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4674(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4675(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4676(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4677(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4678(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4679(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4680(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4681(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4682(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4683(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4684(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4685(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4686(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4687(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4688(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4689(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4690(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4691(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4692(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4693(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4694(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4695(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4696(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4697(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4698(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4699(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4700(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4701(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4702(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4703(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4704(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4705(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4706(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4707(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4708(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4709(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4710(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4711(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4712(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4713(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4714(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4715(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4716(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4717(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4718(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4719(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4720(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4721(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4722(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4723(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4724(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4725(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4726(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4727(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4728(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4729(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4730(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4731(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4732(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4733(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4734(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4735(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4736(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4737(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4738(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4739(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4740(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4741(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4742(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4743(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4744(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4745(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4746(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4747(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4748(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4749(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4750(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4751(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4752(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4753(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4754(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4755(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4756(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4757(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4758(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4759(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4760(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4761(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4762(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4763(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4764(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4765(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4766(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4767(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4768(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4769(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4770(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4771(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4772(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4773(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4774(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4775(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4776(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4777(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4778(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4779(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4780(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4781(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4782(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4783(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4784(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4785(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4786(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4787(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4788(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4789(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4790(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4791(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4792(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4793(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4794(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4795(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4796(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4797(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4798(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4799(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4800(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4801(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4802(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4803(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4804(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4805(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4806(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4807(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4808(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4809(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4810(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4811(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4812(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4813(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4814(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4815(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4816(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4817(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4818(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4819(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4820(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4821(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4822(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4823(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4824(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4825(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4826(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4827(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4828(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4829(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4830(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4831(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4832(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4833(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4834(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4835(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4836(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4837(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4838(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4839(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4840(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4841(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4842(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4843(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4844(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4845(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4846(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4847(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4848(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4849(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4850(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4851(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4852(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4853(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4854(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4855(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4856(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4857(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4858(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4859(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4860(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4861(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4862(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4863(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4864(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4865(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4866(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4867(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4868(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4869(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4870(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4871(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4872(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4873(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4874(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4875(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4876(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4877(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4878(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4879(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4880(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4881(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4882(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4883(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4884(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4885(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4886(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4887(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4888(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4889(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4890(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4891(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4892(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4893(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4894(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4895(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4896(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4897(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4898(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4899(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4900(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4901(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4902(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4903(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4904(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4905(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4906(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4907(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4908(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4909(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4910(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4911(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4912(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4913(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4914(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4915(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4916(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4917(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4918(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4919(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4920(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4921(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4922(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4923(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4924(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4925(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4926(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4927(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4928(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4929(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4930(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4931(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4932(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4933(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4934(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4935(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4936(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4937(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4938(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4939(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4940(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4941(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4942(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4943(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4944(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4945(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4946(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4947(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4948(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4949(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4950(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4951(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4952(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4953(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4954(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4955(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4956(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4957(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4958(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4959(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4960(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4961(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4962(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4963(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4964(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4965(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4966(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4967(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4968(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4969(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4970(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4971(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4972(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4973(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4974(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4975(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4976(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4977(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4978(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4979(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4980(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4981(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4982(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4983(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4984(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4985(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4986(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4987(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4988(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4989(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4990(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4991(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4992(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4993(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4994(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4995(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4996(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4997(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4998(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
define i64 @f4999(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}

define i64 @loop(i64 %n) {
entry:
  br label %header
header:
  %i = phi i64 [ 0, %entry ], [ %i.next, %body ]
  %cond = icmp slt i64 %i, %n
  br i1 %cond, label %body, label %exit
body:
  %i.next = call i64 @f4999(i64 %i)
  br label %header
exit:
  ret i64 %i
}

define i64 @main(i64 %argc, i8** %argv) {
  %r = call i64 @loop(i64 40000)
  ret i64 %r
}

; ASSERT EQ: i64 40000 = call i64 @main(i64 0, i8** null)
