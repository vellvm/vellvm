#!/usr/bin/env python3
"""Run every tests/ub case under Vellvm, llubi, and natively compiled clang
(-O0..-O3 and AddressSanitizer), one case per process, and tabulate the results.

    cd src && make interp            # builds ./vellvm
    python3 ../tests/ub/compare.py   # writes ../tests/ub/results/compare.{md,json}

Options: --vellvm PATH, --clang PATH, --llubi PATH, --out DIR, -j N, and file
paths to restrict the run (default: every .ll under tests/ub).

The cases are the `ASSERT` lines of each file, numbered as by
`tests/gen.py --dispatch`, which must have been run on the file (it provides
@ub_case_N for llubi and the `main N` dispatcher for the native builds).
"""
import argparse
import concurrent.futures as cf
import datetime
import glob
import json
import os
import platform
import re
import shutil
import signal
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
sys.dont_write_bytecode = True  # don't leave tests/__pycache__ behind
sys.path.insert(0, os.path.dirname(HERE))
from gen import parse_asserts  # noqa: E402

NATIVE = [("O0", ["-O0"]), ("O1", ["-O1"]), ("O2", ["-O2"]), ("O3", ["-O3"]),
          ("ASan", ["-O0", "-g", "-fsanitize=address"])]
TIMEOUT = 10


def run(cmd, cwd=None, timeout=TIMEOUT, env=None):
    try:
        p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True,
                           timeout=timeout, env=env, errors="replace")
        return p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired:
        return None, "", ""


def short(s, n=70):
    s = " ".join(s.split())
    return s if len(s) <= n else s[:n - 1] + "…"

# -------------------------------------------------------------------- Vellvm


SPAN_MSG = re.compile(r"\[([^\[\]]+?):(\d+)\.\d+-(\d+)\.\d+\]: (?!\[)(.*)")
SPAN = re.compile(r"\[([^\[\]]+?):(\d+)\.\d+-(\d+)\.\d+\]")


def vellvm_case(vellvm, path, text, a, tmpdir):
    """Run one assertion of `path` through the Vellvm test harness, with every
    other assertion commented out (line numbers are preserved)."""
    lines = text.split("\n")
    for i, l in enumerate(lines, 1):
        if i != a["line"] and re.match(r"\s*;\s*ASSERT", l):
            lines[i - 1] = "; (assertion disabled by compare.py)"
    tmp = os.path.join(tmpdir, os.path.basename(path))
    with open(tmp, "w") as f:
        f.write("\n".join(lines))
    # Vellvm writes scratch files (.ll_files_N.tmp) into its working
    # directory, so each run gets its own.
    libll = os.path.join(os.path.dirname(vellvm), "libll")
    rc, out, err = run([vellvm, "-L", libll, "-test-file", tmp], cwd=tmpdir)
    o = out + err
    base = os.path.basename(path)

    def where(f, l1):
        return f"L{l1}" if os.path.basename(f) == base else f"{os.path.basename(f)}:{l1}"
    if rc is None:
        return dict(kind="timeout", text="timeout")
    if "Parsing error" in o:
        return dict(kind="error", text="parse error")
    passed = "Passed: 1/1" in o
    ub = None
    for m in SPAN_MSG.finditer(o):
        ub = dict(kind="UB", file=m[1], line=int(m[2]), line2=int(m[3]),
                  text=f"UB {where(m[1], m[2])}: {m[4].strip()}")
        break
    if passed:
        if a["kind"] == "UB":
            return ub or dict(kind="UB", text="UB")
        return dict(kind="value", text="as asserted")
    m = re.search(r"ERROR: (.*)", o)
    err_line = m[1] if m else o.strip().splitlines()[-1] if o.strip() else "?"
    if "Undefined Behavior" in err_line:
        if ub:
            return ub
        s = SPAN.search(err_line)
        return dict(kind="UB", text="UB" + (f" {where(s[1], s[2])}" if s else ""))
    m = re.search(r"but got (.*)", err_line)
    if m:
        return dict(kind="value", text=f"= {m[1].strip()}")
    if "ASSERT EQ failed" in err_line:
        m = re.search(r"got:\s*\n\s*(.*)", o)
        return dict(kind="value", text=f"= {m[1].strip()}" if m else "≠ asserted")
    s = SPAN.search(err_line)
    msg = SPAN.sub("", err_line).strip(" :")
    return dict(kind="error", text=short(msg or err_line, 60) + (f" ({where(s[1], s[2])})" if s else ""))

# --------------------------------------------------------------------- llubi


def llubi_case(llubi, path, n, extra):
    rc, out, err = run([llubi, *extra, f"--entry-function=ub_case_{n}", path])
    o = out + err
    if rc is None:
        return dict(kind="timeout", text="timeout")
    m = re.search(r"Immediate UB detected: (.*)", o)
    if m:
        # Frame #0 is where the UB happened.  If that is the generated
        # @ub_case_N wrapper, llubi blamed the call into the test (e.g. a
        # noundef return value is checked by the caller).
        loc = re.search(r"#0 .* at @(\S+) (\S+?):(\d+)", o)
        if loc and loc[1].startswith("ub_case_"):
            return dict(kind="UB", line=-1, text=f"UB at call in wrapper: {m[1].strip()}")
        r = dict(kind="UB", text=f"UB{' L' + loc[3] if loc else ''}: {m[1].strip()}")
        if loc:
            r["line"] = int(loc[3])
        return r
    if "poison return value" in o:
        return dict(kind="value", text="poison")
    m = re.search(r"Unrecognized instruction:\s*(?:%\S+ = )?(\w+)", o)
    if m:
        return dict(kind="error", text=f"unsupported: {m[1]}")
    m = re.search(r"error: (.*)", o)
    if m:
        return dict(kind="error", text=short(m[1], 60))
    return dict(kind="value", text="ok")

# -------------------------------------------------------------------- native


def with_sanitize_address(path, bindir):
    """A copy of `path` whose functions carry `sanitize_address`.  clang adds
    that attribute when compiling C, but not to .ll input, and the ASan pass
    only instruments functions that have it."""
    text = re.sub(r"^(define\b.*?)\s*\{\s*$", r"\1 sanitize_address {",
                  open(path).read(), flags=re.M)
    tmp = os.path.join(bindir, re.sub(r"\W", "_", os.path.relpath(path, HERE)) + ".asan.ll")
    with open(tmp, "w") as f:
        f.write(text)
    return tmp


def build(clang, path, bindir):
    builds = {}
    for name, flags in NATIVE:
        exe = os.path.join(bindir, re.sub(r"\W", "_", os.path.relpath(path, HERE)) + "." + name)
        src = with_sanitize_address(path, bindir) if "-fsanitize=address" in flags else path
        rc, out, err = run([clang, "-w", *flags, src, "-o", exe], timeout=120)
        builds[name] = exe if rc == 0 else short("build failed: " + next(
            (l for l in (out + err).splitlines() if "error" in l), "?"), 60)
    return builds


def native_case(exe, n):
    env = dict(os.environ, ASAN_OPTIONS="detect_leaks=0:abort_on_error=0:detect_stack_use_after_return=1")
    rc, out, err = run([exe, str(n)], env=env)
    if rc is None:
        return dict(kind="timeout", text="timeout")
    m = re.search(r"ERROR: AddressSanitizer: (.+?)(?::| on | at pc|$)", err, re.M)
    if m:
        return dict(kind="UB", text=f"ASan: {m[1].strip()}")
    m = re.search(rf"case {n}: returned(.*)", out)
    if rc == 0 and m:
        return dict(kind="value", text=f"={m[1]}" if m[1].strip() else "returned")
    if rc < 0:
        try:
            sig = signal.Signals(-rc).name
        except ValueError:
            sig = f"signal {-rc}"
        return dict(kind="trap", text=sig)
    if f"case {n}: start" in out and not m:
        return dict(kind="trap", text=f"no return (exit {rc})")
    return dict(kind="error", text=f"exit {rc}")

# ------------------------------------------------------------------- driver


def expected(a):
    if a["kind"] == "UB":
        return f"UB L{a['ubline']}"
    if a["kind"] == "EQ":
        return f"= {a['expected']}"
    return a["kind"].lower()


def verdict(a, r):
    """✓ if a tool result agrees with the assertion, ~ for UB on the wrong
    line, ✗ otherwise."""
    if a["kind"] == "UB":
        if r["kind"] != "UB":
            return "✗"
        if "line" in r and r["line"] != a["ubline"]:
            if not (r.get("line2") and r["line"] <= a["ubline"] <= r["line2"]):
                return "~"
        return "✓"
    return "✗" if r["kind"] in ("UB", "error", "timeout") else "✓"


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("files", nargs="*")
    ap.add_argument("--vellvm", default=os.path.join(REPO, "src", "vellvm"))
    ap.add_argument("--clang", default=shutil.which("clang") or "clang")
    ap.add_argument("--llubi", default=shutil.which("llubi") or "llubi")
    ap.add_argument("--out", default=os.path.join(HERE, "results"))
    ap.add_argument("-j", type=int, default=os.cpu_count())
    args = ap.parse_args()
    files = [os.path.abspath(f) for f in args.files] or sorted(
        glob.glob(os.path.join(HERE, "**", "*.ll"), recursive=True))
    vellvm = os.path.abspath(args.vellvm)
    work = tempfile.mkdtemp(prefix="ub-compare-")
    bindir = os.path.join(work, "bin")
    os.makedirs(bindir)

    jobs = []  # (file, case index, assertion)
    texts = {}
    for f in files:
        texts[f] = open(f).read()
        if "BEGIN executable tail" not in texts[f]:
            sys.exit(f"{f}: no executable tail; run tests/gen.py --dispatch on it first")
        for n, a in enumerate(parse_asserts(texts[f])):
            jobs.append((f, n, a))

    with cf.ThreadPoolExecutor(args.j) as ex:
        builds = dict(zip(files, ex.map(lambda f: build(args.clang, f, bindir), files)))

        def one(job):
            f, n, a = job
            d = tempfile.mkdtemp(dir=work)
            r = {"Vellvm": vellvm_case(vellvm, f, texts[f], a, d),
                 "llubi": llubi_case(args.llubi, f, n, []),
                 "llubi-z": llubi_case(args.llubi, f, n, ["--undef-behavior=zero"])}
            for name, _ in NATIVE:
                exe = builds[f][name]
                r[name] = (native_case(exe, n) if os.path.isfile(exe)
                           else dict(kind="error", text=exe))
            return r
        results = list(ex.map(one, jobs))
    shutil.rmtree(work, ignore_errors=True)

    tools = ["Vellvm", "llubi", "llubi-z"] + [n for n, _ in NATIVE]
    rows = []
    for (f, n, a), r in zip(jobs, results):
        rows.append(dict(file=os.path.relpath(f, HERE), case=n, line=a["line"],
                         assertion=a["src"], expected=expected(a), kind=a["kind"],
                         results={t: dict(r[t], verdict=verdict(a, r[t])) for t in tools}))

    os.makedirs(args.out, exist_ok=True)
    meta = dict(date=datetime.date.today().isoformat(),
                platform=f"{platform.system()} {platform.machine()}",
                vellvm_commit=run(["git", "rev-parse", "--short", "HEAD"], cwd=REPO)[1].strip(),
                clang=run([args.clang, "--version"])[1].splitlines()[0],
                llubi=" ".join(run([args.llubi, "--version"])[1].split()[:4]))
    with open(os.path.join(args.out, "compare.json"), "w") as fh:
        json.dump(dict(meta=meta, rows=rows), fh, indent=1, ensure_ascii=False)
    with open(os.path.join(args.out, "compare.md"), "w") as fh:
        fh.write(markdown(meta, rows, tools))
    print(summary(rows, tools))
    print(f"wrote {os.path.relpath(args.out)}/compare.md and compare.json")


def summary(rows, tools):
    ub = [r for r in rows if r["kind"] == "UB"]
    ctl = [r for r in rows if r["kind"] != "UB"]
    out = ["| | " + " | ".join(tools) + " |", "|---" * (len(tools) + 1) + "|"]

    native = {n for n, _ in NATIVE}
    levels = ["O0", "O1", "O2", "O3"]

    def count(rs, pred, only=None):
        return [str(sum(1 for r in rs if pred(r["results"][t])))
                if only is None or (t in native) == only else "–" for t in tools]

    def row(label, cells):
        out.append(f"| {label} | " + " | ".join(cells) + " |")

    def differs(r):
        return len({r["results"][t]["text"] for t in levels}) > 1
    row(f"UB cases reported as UB ({len(ub)})",
        count(ub, lambda x: x["kind"] == "UB", only=False))
    row("… on the asserted line", count(ub, lambda x: x["kind"] == "UB" and x["verdict"] == "✓", only=False))
    row(f"UB cases that trap, hang, or fail an ASan check ({len(ub)})",
        count(ub, lambda x: x["kind"] in ("UB", "trap", "timeout"), only=True))
    row(f"controls reported as UB / trapping ({len(ctl)})",
        count(ctl, lambda x: x["kind"] in ("UB", "trap", "timeout")))
    row("errors (unsupported, build/parse failures)", count(rows, lambda x: x["kind"] == "error"))
    out += ["", f"Native output differs between -O0..-O3: {sum(map(differs, ub))} of "
            f"{len(ub)} UB cases, {sum(map(differs, ctl))} of {len(ctl)} controls."]
    return "\n".join(out)


def markdown(meta, rows, tools):
    out = ["# tests/ub comparison", "",
           f"Generated by `tests/ub/compare.py` on {meta['date']} ({meta['platform']}, "
           f"Vellvm {meta['vellvm_commit']}, {meta['clang']}, {meta['llubi']}).", "",
           "Each case runs alone: Vellvm through its test harness with only that "
           "assertion enabled; llubi with `--entry-function=ub_case_N` (`llubi-z` adds "
           "`--undef-behavior=zero`); native builds as `./a.out N`.", "",
           "Vellvm/llubi cells: `UB L<line>: <reason>`, a value, or an error. "
           "Native cells: `= <printed result>`, a signal, `no return`, `timeout`, or "
           "`ASan: <report>`. Marks: ✓ agrees with the assertion, ~ UB on a different "
           "line, ✗ disagrees (native columns are not marked: they are not UB detectors).",
           "", "## Summary", "", summary(rows, tools), ""]
    native = {n for n, _ in NATIVE}
    for f in sorted({r["file"] for r in rows}, key=lambda s: (s.count("/"), s)):
        out += [f"## {f}", "",
                "| # | assertion | expected | " + " | ".join(tools) + " |",
                "|---" * (len(tools) + 3) + "|"]
        for r in (r for r in rows if r["file"] == f):
            cells = []
            for t in tools:
                x = r["results"][t]
                txt = short(x["text"], 50).replace("|", "\\|")
                cells.append(txt if t in native else f"{x['verdict']} {txt}")
            asrt = short(re.sub(r"^ASSERT\s+", "", r["assertion"]), 60).replace("|", "\\|")
            out.append(f"| {r['case']} | L{r['line']} `{asrt}` | {r['expected']} | "
                       + " | ".join(cells) + " |")
        out.append("")
    return "\n".join(out)


if __name__ == "__main__":
    main()
