#!/usr/bin/env python3
"""Regenerate switch-cases.ll with a different case count / loop bound."""
import sys

C = int(sys.argv[1]) if len(sys.argv) > 1 else 256
K = int(sys.argv[2]) if len(sys.argv) > 2 else 8192

assert K % C == 0, "K must be a multiple of C for the closed form"
result = K * (C - 1) // 2

lines = []
lines.append("; PERF: switch dispatch vs. case count.")
lines.append("; A loop switching on i mod %d over %d cases. denote_terminator" % (C, C))
lines.append("; re-elaborates every case literal (coerce_integer_to_int via")
lines.append("; map_monad) on each execution before the linear select_switch scan,")
lines.append("; so a switch hit costs ~2 us per case: this test spends most of its")
lines.append("; time re-processing constants. Pre-elaborating the cases (they are")
lines.append("; syntactically constant) would make this test collapse toward")
lines.append("; loop-phi-arith.ll's per-iteration cost.")
lines.append(";")
lines.append("; Tune: regenerate with a different C / K (see perf/README.md).")
lines.append("; Result is sum of (i mod C) for i in [0,K) = K*(C-1)/2.")
lines.append("")
lines.append("define i64 @main(i64 %argc, i8** %argv) {")
lines.append("entry:")
lines.append("  br label %header")
lines.append("header:")
lines.append("  %i = phi i64 [ 0, %entry ], [ %i.next, %latch ]")
lines.append("  %acc = phi i64 [ 0, %entry ], [ %acc.next, %latch ]")
lines.append("  %c = icmp eq i64 %i, " + str(K))
lines.append("  br i1 %c, label %exit, label %sw")
lines.append("sw:")
lines.append("  %m = urem i64 %i, " + str(C))
cases = " ".join("i64 %d, label %%case%d" % (j, j) for j in range(C))
lines.append("  switch i64 %m, label %case0 [ " + cases + " ]")
for j in range(C):
    lines.append("case%d:" % j)
    lines.append("  br label %join")
lines.append("join:")
lines.append("  br label %latch")
lines.append("latch:")
lines.append("  %acc.next = add i64 %acc, %m")
lines.append("  %i.next = add i64 %i, 1")
lines.append("  br label %header")
lines.append("exit:")
lines.append("  ret i64 %acc")
lines.append("}")
lines.append("")
lines.append("; ASSERT EQ: i64 %d = call i64 @main(i64 0, i8** null)" % result)

with open("switch-cases.ll", "w") as f:
    f.write("\n".join(lines) + "\n")
print("wrote switch-cases.ll with C = %d, K = %d, expected result %d" % (C, K, result))
