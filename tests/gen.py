"""Append the executable tail to a Vellvm test body.

Tests in the style of tests/ll/aggregate-poison.ll define one `i64`-returning
function per case, then end with a `main` that prints each result (so the
file can be run natively and its output diffed against clang) and an
`ASSERT EQ` per function (for the Vellvm test harness).  This script writes
that tail, getting the printf format-string array lengths right.

Usage:
    python3 tests/gen.py BODY.ll SPEC > tests/ll/NAME.ll

BODY.ll holds the header comment and the test functions.  SPEC has one line
per test, `<function-name> <expected-i64-result>`, in the order the results
should be printed, e.g.

    store_byte_constant 42
    bitcast_byte_constant 1000
"""
import sys
def tail(tests):
    """tests: list of (fname, expected). Emits the executable main + ASSERTs."""
    out = ["", "; --- executable form: print each result so the file can be run and",
           "; --- its output diffed against clang/llc.", ""]
    for f, _ in tests:
        s = f"{f}() = %lld\\0A\\00"
        n = len(f) + len("() = %lld") + 2
        out.append(f'@fmt_{f} = private unnamed_addr constant [{n} x i8] c"{s}"')
    out += ["", "declare i32 @printf(ptr, ...)", "", "define i32 @main() {"]
    for i, (f, _) in enumerate(tests):
        out.append(f"  %v{i} = call i64 @{f}()")
        out.append(f"  %p{i} = call i32 (ptr, ...) @printf(ptr @fmt_{f}, i64 %v{i})")
    out += ["  ret i32 0", "}", ""]
    w = max(len(str(e)) for _, e in tests)
    for f, e in tests:
        out.append(f"; ASSERT EQ: i64 {str(e).ljust(w)} = call i64 @{f}()")
    return "\n".join(out) + "\n"
body, spec = sys.argv[1], sys.argv[2]
tests = [(l.split()[0], l.split()[1]) for l in open(spec) if l.strip()]
sys.stdout.write(open(body).read() + tail(tests))
