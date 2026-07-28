#!/usr/bin/env python3
"""Regenerate locals-chain.ll with a different number of temporaries."""
import sys

N = int(sys.argv[1]) if len(sys.argv) > 1 else 10000

lines = []
lines.append("; PERF: local-environment growth.")
lines.append("; A single straight-line function defining %d distinct temporaries," % N)
lines.append("; each reading the previous one. The local env gains one binding per")
lines.append("; instruction and every read searches it, so an association-list env")
lines.append("; makes this quadratic while a tree map keeps it n log n. Compare")
lines.append("; against loop-phi-arith.ll (same kind of instructions, constant-size")
lines.append("; env) to isolate the env-scaling cost.")
lines.append(";")
lines.append("; Tune: regenerate with a different N (see tests/perf/README.md).")
lines.append("; Result is sum 1..N = N*(N+1)/2.")
lines.append("")
lines.append("define i64 @chain() {")
lines.append("  %x0 = add i64 0, 0")
for k in range(1, N + 1):
    lines.append("  %%x%d = add i64 %%x%d, %d" % (k, k - 1, k))
lines.append("  ret i64 %%x%d" % N)
lines.append("}")
lines.append("")
lines.append("define i64 @main(i64 %argc, i8** %argv) {")
lines.append("  %r = call i64 @chain()")
lines.append("  ret i64 %r")
lines.append("}")
lines.append("")
lines.append("; ASSERT EQ: i64 %d = call i64 @main(i64 0, i8** null)" % (N * (N + 1) // 2))

with open("locals-chain.ll", "w") as f:
    f.write("\n".join(lines) + "\n")
print("wrote locals-chain.ll with N = %d, expected result %d" % (N, N * (N + 1) // 2))
