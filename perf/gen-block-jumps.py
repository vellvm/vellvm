#!/usr/bin/env python3
"""Regenerate block-jumps.ll with a different block count / loop bound."""
import sys

D = int(sys.argv[1]) if len(sys.argv) > 1 else 6400
K = int(sys.argv[2]) if len(sys.argv) > 2 else 100000

lines = []
lines.append("; PERF: per-jump block-target resolution in a large function.")
lines.append("; A tight 3-block counted loop placed after %d unreachable blocks," % D)
lines.append("; so every jump resolves a block id against a %d-block function." % (D + 5))
lines.append("; A linear find_block scan pays O(position) per jump, making this")
lines.append("; ~9x slower than with the AVL block map; the dead blocks are never")
lines.append("; executed, so any slowdown relative to loop-phi-arith.ll (same hot")
lines.append("; loop, tiny function) is pure lookup cost.")
lines.append(";")
lines.append("; Tune: regenerate with a different D / K (see perf/README.md).")
lines.append("; Result is sum 0..(K-1) = K*(K-1)/2.")
lines.append("")
lines.append("define i64 @jumps(i64 %n) {")
lines.append("entry:")
lines.append("  br label %header")
for i in range(D):
    lines.append("dead%d:" % i)
    lines.append("  ret i64 -1")
lines.append("header:")
lines.append("  %i = phi i64 [ 0, %entry ], [ %i.next, %latch ]")
lines.append("  %acc = phi i64 [ 0, %entry ], [ %acc.next, %latch ]")
lines.append("  %cond = icmp slt i64 %i, %n")
lines.append("  br i1 %cond, label %body, label %exit")
lines.append("body:")
lines.append("  %acc.next = add i64 %acc, %i")
lines.append("  br label %latch")
lines.append("latch:")
lines.append("  %i.next = add i64 %i, 1")
lines.append("  br label %header")
lines.append("exit:")
lines.append("  ret i64 %acc")
lines.append("}")
lines.append("")
lines.append("define i64 @main(i64 %argc, i8** %argv) {")
lines.append("  %%r = call i64 @jumps(i64 %d)" % K)
lines.append("  ret i64 %r")
lines.append("}")
lines.append("")
lines.append("; ASSERT EQ: i64 %d = call i64 @main(i64 0, i8** null)" % (K * (K - 1) // 2))

with open("block-jumps.ll", "w") as f:
    f.write("\n".join(lines) + "\n")
print("wrote block-jumps.ll with D = %d, K = %d, expected result %d"
      % (D, K, K * (K - 1) // 2))
