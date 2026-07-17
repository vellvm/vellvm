#!/usr/bin/env python3
"""Regenerate calls-many-fns.ll with a different function count / call count."""
import sys

N = int(sys.argv[1]) if len(sys.argv) > 1 else 5000
K = int(sys.argv[2]) if len(sys.argv) > 2 else 40000

lines = []
lines.append("; PERF: per-call function-pointer dispatch vs. module size.")
lines.append("; A module with %d trivial functions; a counted loop calls the" % N)
lines.append("; last-defined one %d times. Function dispatch (lookup_defn in" % K)
lines.append("; denote_mcfg) resolves the callee's address in an AVL IntMap built")
lines.append("; once in TopLevel, so per-call cost stays flat in the number of")
lines.append("; definitions; an association-list dispatch (as upstream) scans the")
lines.append("; definitions per call and makes this test blow up, as would")
lines.append("; rebuilding the map per call. Compare per-call cost against")
lines.append("; calls-fib.ll (many calls, two functions) and calls-large-fn.ll")
lines.append("; (per-call setup vs. callee size).")
lines.append(";")
lines.append("; Tune: regenerate with a different N / K (see perf/README.md).")
lines.append("; Result is K (the callee is the successor function).")
lines.append("")
for i in range(N):
    lines.append("define i64 @f%d(i64 %%x) {" % i)
    lines.append("  %r = add i64 %x, 1")
    lines.append("  ret i64 %r")
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
lines.append("  %%i.next = call i64 @f%d(i64 %%i)" % (N - 1))
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

with open("calls-many-fns.ll", "w") as f:
    f.write("\n".join(lines) + "\n")
print("wrote calls-many-fns.ll with N = %d, K = %d, expected result %d" % (N, K, K))
