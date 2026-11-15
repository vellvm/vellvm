#!/usr/bin/env python3
"""Generate int-intrinsics.ll: the integer intrinsics at i8, i32 and i64.

One function per intrinsic and width, called on a few boundary operands.
The expected values are not modelled here: the calls are compiled with
clang -O0 and run, and what they print becomes the assertions.  Operands
whose result is poison are left out (tests/llvm-arith/i1 covers those).

    python3 gen-int-intrinsics.py        # needs clang on the PATH
"""
import os, subprocess, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
WIDTHS = (8, 32, 64)

def lit(w, u):
    """LLVM wants signed literals."""
    u %= 1 << w
    return str(u - (1 << w) if u >= 1 << (w - 1) else u)

decls, defs, calls = [], [], []     # calls: (function, argument string)

def define(fn, params, body, ty, res="%r"):
    """A wrapper returning the result zero-extended to i64."""
    lines = [f"define i64 @{fn}({params}) {{"] + ["  " + l for l in body]
    if ty != "i64":
        lines.append(f"  %z = zext {ty} {res} to i64")
        res = "%z"
    defs.append("\n".join(lines + [f"  ret i64 {res}", "}"]))

for w in WIDTHS:
    m, t = 1 << w, f"i{w}"
    smax, smin, pat = m // 2 - 1, m // 2, 0x5a5a5a5a5a5a5a5a % m
    pairs = [(0, 1), (smax, 1), (smin, m - 1), (smin, smin), (m - 1, m - 1), (pat, 2), (1, smax)]
    ones = [0, 1, smax, smin, m - 1, pat]

    def args(*vs):
        return ", ".join(f"{t} {lit(w, v)}" for v in vs)

    def binary(k, body, ty, decl):
        fn = f"{k.replace('.', '_')}_{t}"
        decls.append(decl)
        define(fn, f"{t} %a, {t} %b", body, ty)
        calls.extend((fn, args(a, b)) for a, b in pairs)

    for k in ("smax", "smin", "umax", "umin", "sadd.sat", "ssub.sat", "uadd.sat", "usub.sat"):
        binary(k, [f"%r = call {t} @llvm.{k}.{t}({t} %a, {t} %b)"], t,
               f"declare {t} @llvm.{k}.{t}({t}, {t})")
    for k in ("sadd", "ssub", "smul", "uadd", "usub", "umul"):
        s = f"{{ {t}, i1 }}"
        call = f"%p = call {s} @llvm.{k}.with.overflow.{t}({t} %a, {t} %b)"
        binary(f"{k}.value", [call, f"%r = extractvalue {s} %p, 0"], t,
               f"declare {s} @llvm.{k}.with.overflow.{t}({t}, {t})")
        fn = f"{k}_overflows_{t}"
        define(fn, f"{t} %a, {t} %b", [call, f"%r = extractvalue {s} %p, 1"], "i1")
        calls.extend((fn, args(a, b)) for a, b in pairs)
    for k in ("scmp", "ucmp"):
        r = "i2" if w == 8 else "i8"
        binary(k, [f"%r = call {r} @llvm.{k}.{r}.{t}({t} %a, {t} %b)"], r,
               f"declare {r} @llvm.{k}.{r}.{t}({t}, {t})")

    for k in ("sshl.sat", "ushl.sat"):
        fn = f"{k.replace('.', '_')}_{t}"
        decls.append(f"declare {t} @llvm.{k}.{t}({t}, {t})")
        define(fn, f"{t} %a, {t} %b", [f"%r = call {t} @llvm.{k}.{t}({t} %a, {t} %b)"], t)
        calls.extend((fn, args(a, s)) for a in (1, smax, m - 1, pat) for s in (0, 1, w - 1))

    for k, poison_at in (("abs", smin), ("ctlz", 0), ("cttz", 0)):
        fn = f"{k}_{t}"
        decls.append(f"declare {t} @llvm.{k}.{t}({t}, i1)")
        for flag in (0, 1):
            define(f"{fn}_{flag}", f"{t} %a", [f"%r = call {t} @llvm.{k}.{t}({t} %a, i1 {flag})"], t)
            calls.extend((f"{fn}_{flag}", args(a)) for a in ones if not (flag and a == poison_at))
    for k in ("ctpop", "bitreverse"):
        fn = f"{k}_{t}"
        decls.append(f"declare {t} @llvm.{k}.{t}({t})")
        define(fn, f"{t} %a", [f"%r = call {t} @llvm.{k}.{t}({t} %a)"], t)
        calls.extend((fn, args(a)) for a in ones)

    for k in ("fshl", "fshr"):
        fn = f"{k}_{t}"
        decls.append(f"declare {t} @llvm.{k}.{t}({t}, {t}, {t})")
        define(fn, f"{t} %a, {t} %b, {t} %c",
               [f"%r = call {t} @llvm.{k}.{t}({t} %a, {t} %b, {t} %c)"], t)
        calls.extend((fn, args(a, b, c)) for a, b in ((pat, 1), (smin, m - 1), (1, smin))
                     for c in (0, 1, w - 1, w + 3))

    v = f"<4 x {t}>"
    for k in ("add", "mul", "and", "or", "xor", "smax", "smin", "umax", "umin"):
        fn = f"reduce_{k}_{t}"
        decls.append(f"declare {t} @llvm.vector.reduce.{k}.v4{t}({v})")
        define(fn, f"{v} %v", [f"%r = call {t} @llvm.vector.reduce.{k}.v4{t}({v} %v)"], t)
        calls.extend((fn, f"{v} <{args(*elts)}>")
                     for elts in ((1, smax, m - 1, 2), (pat, smin, 3, pat), (smax, smax, 1, 0)))

prelude = "\n".join(decls) + "\n\n" + "\n\n".join(defs) + "\n\n"

main = ['@fmt = private constant [6 x i8] c"%llu\\0A\\00"', "declare i32 @printf(ptr, ...)",
        "define i32 @main() {"]
for i, (fn, a) in enumerate(calls):
    main += [f"  %v{i} = call i64 @{fn}({a})", f"  call i32 (ptr, ...) @printf(ptr @fmt, i64 %v{i})"]
main += ["  ret i32 0", "}"]

with tempfile.TemporaryDirectory() as d:
    src, exe = os.path.join(d, "oracle.ll"), os.path.join(d, "oracle")
    with open(src, "w") as f:
        f.write(prelude + "\n".join(main) + "\n")
    subprocess.run(["clang", "-w", "-O0", src, "-o", exe], check=True)
    expected = subprocess.run([exe], check=True, capture_output=True, text=True).stdout.split()
assert len(expected) == len(calls)

header = """; Integer intrinsics at i8, i32 and i64.
;
; Generated by gen-int-intrinsics.py; do not edit.  Each function returns the
; result of one intrinsic, zero-extended to i64; the expected values are what
; the same calls return when compiled with clang -O0.

"""
with open(os.path.join(HERE, "int-intrinsics.ll"), "w") as f:
    f.write(header + prelude)
    for (fn, a), e in zip(calls, expected):
        f.write(f"; ASSERT EQ: i64 {e} = call i64 @{fn}({a})\n")
print(len(calls), "assertions,", len(defs), "functions")
