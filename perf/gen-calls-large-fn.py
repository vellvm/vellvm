#!/usr/bin/env python3
"""Regenerate calls-large-fn.ll with a different callee size / call count."""
import sys

D = int(sys.argv[1]) if len(sys.argv) > 1 else 400
K = int(sys.argv[2]) if len(sys.argv) > 2 else 40000

lines = []
lines.append("; PERF: per-call denotation setup cost as a function of callee size.")
lines.append("; A trivial callee padded with %d unreachable blocks, called %d" % (D, K))
lines.append("; times from a counted loop. Any per-call work proportional to the")
lines.append("; callee's block count shows up here multiplied by the call count --")
lines.append("; e.g. building the block-id map per call instead of once per")
lines.append("; definition (in denote_function) made this test ~4x slower, and")
lines.append("; hundreds of times slower at larger D. Compare per-call cost against")
lines.append("; calls-fib.ll (many calls, minimal callee).")
lines.append(";")
lines.append("; Tune: regenerate with a different D / K (see perf/README.md).")
lines.append("; Result is K (the callee is the successor function).")
lines.append("")
lines.append("define i64 @f(i64 %x) {")
lines.append("entry:")
lines.append("  %r = add i64 %x, 1")
lines.append("  ret i64 %r")
for i in range(D):
    lines.append("dead%d:" % i)
    lines.append("  ret i64 -1")
lines.append("}")
lines.append("")
lines.append("define i64 @loop(i64 %n) {")
lines.append("entry:")
lines.append("  br label %header")
lines.append("header:")
lines.append("  %i = phi i64 [ 0, %entry ], [ %i.next, %body ]")
lines.append("  %cond = icmp slt i64 %i, %n")
lines.append("  br i1 %cond, label %body, label %exit")
lines.append("body:")
lines.append("  %i.next = call i64 @f(i64 %i)")
lines.append("  br label %header")
lines.append("exit:")
lines.append("  ret i64 %i")
lines.append("}")
lines.append("")
lines.append("define i64 @main(i64 %argc, i8** %argv) {")
lines.append("  %%r = call i64 @loop(i64 %d)" % K)
lines.append("  ret i64 %r")
lines.append("}")
lines.append("")
lines.append("; ASSERT EQ: i64 %d = call i64 @main(i64 0, i8** null)" % K)

with open("calls-large-fn.ll", "w") as f:
    f.write("\n".join(lines) + "\n")
print("wrote calls-large-fn.ll with D = %d, K = %d, expected result %d" % (D, K, K))
