#!/usr/bin/env python3
"""Extract the illustrative examples from the LLVM Language Reference Manual.

The LangRef gives, for most instructions, an ``Example:`` block showing the
instruction in use.  Those blocks are fragments, not programs: they use a
literal ``<result> =`` placeholder, reference undefined variables, and state
their outcome in prose (``; yields i32:result = 4 + %var``).  They therefore
cannot be turned into executable tests mechanically -- choosing concrete
inputs and working out the expected output is hand work.

What *is* mechanical, and what this script does:

  * enumerate every example block, so no instruction is silently skipped;
  * record where each one came from (section anchor + a hash of the verbatim
    example text) inside the generated test, so the suite stays traceable;
  * emit a skeleton test per instruction, with free variables promoted to
    typed parameters, as a starting point for hand completion;
  * re-check a completed suite against a newer LangRef and report drift.

Usage:
    utilities/langref_examples.py generate [--force]   # write skeletons
    utilities/langref_examples.py manifest             # (re)write MANIFEST.md
    utilities/langref_examples.py check                # report drift, exit 1

``generate`` never overwrites an existing test unless ``--force`` is given:
the hand-written assertions are the valuable part.
"""

import argparse
import hashlib
import html
import os
import re
import sys
from collections import OrderedDict

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LANGREF = os.path.join(REPO, "langref.html")
LANGREF_URL = "https://llvm.org/docs/LangRef.html"
OUTDIR = os.path.join(REPO, "tests", "langref")

# Instructions Vellvm does not implement.  Kept in the manifest so the gap is
# visible rather than forgotten.
UNSUPPORTED = {
    "invoke": "exception handling not modelled",
    "callbr": "inline asm / asm goto not modelled",
    "indirectbr": "no indirect branch",
    "resume": "exception handling not modelled",
    "catchswitch": "exception handling not modelled",
    "catchpad": "exception handling not modelled",
    "catchret": "exception handling not modelled",
    "cleanuppad": "exception handling not modelled",
    "cleanupret": "exception handling not modelled",
    "landingpad": "exception handling not modelled",
    "fence": "no concurrency / memory ordering",
    "atomicrmw": "no concurrency / memory ordering",
    "cmpxchg": "no concurrency / memory ordering",
    "addrspacecast": "single address space only",
}

PROVENANCE_RE = re.compile(
    r"^;\s*langref:\s*(?P<anchor>\S+)\s+sha1=(?P<sha>[0-9a-f]{40})\s*$", re.M
)

# One LLVM type: a primitive, a pointer, or one level of vector/array/struct.
# The primitive alternative is a closed keyword list on purpose -- an open
# identifier pattern happily reads "add" or "result" as a type.
PRIM = r"i\d+|float|double|half|bfloat|fp128|x86_fp80|ppc_fp128|ptr|void|token|metadata"
TYPE = (
    r"(?:<\s*\d+\s+x\s+[^<>]+?>"
    r"|\[\s*\d+\s+x\s+[^\[\]]+?\]"
    r"|\{[^{}]*\}"
    r"|%[\w.]+\s*(?=\*)"  # named struct type, only when pointed-to
    r"|\b(?:" + PRIM + r")\b\**)"
)


# --------------------------------------------------------------------------
# extraction


class Example(object):
    def __init__(self, name, title, anchor, code):
        self.name = name  # "shufflevector"
        self.title = title  # "'shufflevector' Instruction"
        self.anchor = anchor  # "shufflevector-instruction"
        self.code = code  # verbatim example text

    @property
    def sha(self):
        return hashlib.sha1(self.code.encode("utf-8")).hexdigest()

    @property
    def path(self):
        return os.path.join(OUTDIR, self.name + ".ll")


def _strip_tags(s):
    return html.unescape(re.sub(r"<[^>]+>", "", s))


def parse_langref(path=LANGREF):
    """Return an OrderedDict name -> Example for every instruction example."""
    with open(path, encoding="utf-8") as f:
        doc = f.read()

    token = re.compile(
        r'<section id="([^"]+)">'
        r"|</section>"
        r"|<h4>(.*?)</h4>"
        r'|<h5>([^<]*)<a class="headerlink"'
        r'|<div class="highlight-[\w+-]+ notranslate"><div class="highlight"><pre>(.*?)</pre>',
        re.S,
    )

    out = OrderedDict()
    stack = []  # [section_id, h4 title or None]
    heading = None

    for m in token.finditer(doc):
        sec_id, h4, h5, code = m.group(1), m.group(2), m.group(3), m.group(4)
        if sec_id is not None:
            stack.append([sec_id, None])
        elif m.group(0) == "</section>":
            if stack:
                stack.pop()
            heading = None
        elif h4 is not None:
            if stack:
                stack[-1][1] = _strip_tags(h4).replace("¶", "").strip()
        elif h5 is not None:
            heading = h5.strip().rstrip(":")
        elif code is not None and heading in ("Example", "Examples"):
            owner = next((s for s in reversed(stack) if s[1]), None)
            if owner is None or "Instruction" not in owner[1]:
                continue  # intrinsics and prose sections: out of scope
            name = instruction_name(owner[1])
            body = _strip_tags(code).rstrip("\n")
            if name in out:  # a section with several example blocks
                out[name].code += "\n" + body
            else:
                out[name] = Example(name, owner[1], owner[0], body)
    return out


def ascii_title(title):
    """LangRef titles use typographic quotes; tests stay ASCII."""
    return title.replace("‘", "'").replace("’", "'")


def instruction_name(title):
    """"'addrspacecast .. to' Instruction" -> "addrspacecast"."""
    t = re.sub(r"[‘’]", "", title)
    t = t.replace(" Instruction", "").strip()
    t = re.sub(r"\s*\.\.\s*to$", "", t)
    return t.strip()


def llvm_version(path=LANGREF):
    with open(path, encoding="utf-8") as f:
        head = f.read(20000)
    m = re.search(r"LLVM ([\w.]+) documentation", head)
    return m.group(1) if m else "unknown"


# --------------------------------------------------------------------------
# skeleton emission


def free_variables(code):
    """Free ``%name`` occurrences, best-effort paired with their LLVM type.

    Returns a list of ``(name, type_or_None)`` in first-occurrence order.
    Purely a convenience for hand completion -- the result is a starting
    point, not something to trust.
    """
    assigned = set(re.findall(r"^\s*(%[\w.]+)\s*=", code, re.M))
    labels = set(re.findall(r"label\s+(%[\w.]+)", code))
    labels |= {"%" + l for l in re.findall(r"^\s*([\w.]+):\s*$", code, re.M)}

    typed = {}
    for line in code.split("\n"):
        # An operand is usually written "<ty> <val>", but a binop's second
        # operand inherits the first's type ("add i32 4, %var").  So sweep the
        # line left to right, remembering the last type token seen.
        last = None
        for m in re.finditer(r"(?P<ty>" + TYPE + r")|(?P<var>%[\w.]+)", line):
            if m.group("ty") is not None:
                last = m.group("ty").strip()
            elif last is not None:
                typed.setdefault(m.group("var"), last)

    seen = OrderedDict()
    for var in re.findall(r"%[\w.]+", code):
        if var in assigned or var in labels or var in seen:
            continue
        seen[var] = typed.get(var)
    return list(seen.items())


def skeleton(ex, version):
    lines = []
    lines.append("; Examples from the LLVM LangRef's %s section." % ascii_title(ex.title))
    lines.append("; langref: %s sha1=%s" % (ex.anchor, ex.sha))
    lines.append(";")
    lines.append("; LangRef %s gives the following example(s):" % version)
    lines.append(";")
    for l in ex.code.split("\n"):
        lines.append(("; " + l).rstrip())
    lines.append("")

    if ex.name in UNSUPPORTED:
        lines.append("; NOT SUPPORTED by Vellvm: %s" % UNSUPPORTED[ex.name])
        lines.append("")
        return "\n".join(lines)

    fvs = free_variables(ex.code)
    params = ", ".join(
        "%s %s" % (ty if ty else "i32 (?)", var) for var, ty in fvs
    )
    lines.append("; TODO: one define per example above; pick concrete inputs and")
    lines.append("; work the expected value out of the LangRef's Semantics prose.")
    lines.append("define i32 @todo(%s) {" % params)
    lines.append("  ret i32 0")
    lines.append("}")
    lines.append("")
    lines.append("; ASSERT EQ: i32 0 = call i32 @todo(...)")
    lines.append("")
    return "\n".join(lines)


# --------------------------------------------------------------------------
# manifest


def status_of(ex):
    if ex.name in UNSUPPORTED:
        return "unsupported", UNSUPPORTED[ex.name]
    if not os.path.exists(ex.path):
        return "missing", "no test file"
    with open(ex.path, encoding="utf-8") as f:
        body = f.read()
    if "; TODO" in body:
        return "todo", "skeleton only"
    n = len(re.findall(r"^\s*;\s*ASSERT\b", body, re.M))
    # An assertion the harness would run is written ";ASSERT"; one disabled
    # because Vellvm cannot yet meet it is written ";;ASSERT" next to a
    # "VELLVM GAP" note explaining why.
    gaps = len(re.findall(r"^\s*;;\s*ASSERT\b", body, re.M))
    note = "%d assertion%s" % (n, "" if n == 1 else "s")
    if gaps:
        note += ", %d disabled (Vellvm gap)" % gaps
    return ("gap" if gaps else "done"), note


def write_manifest(examples, version):
    rows = []
    for ex in examples.values():
        st, note = status_of(ex)
        rows.append((ex.name, st, note, ex.anchor))

    counts = {}
    for _, st, _, _ in rows:
        counts[st] = counts.get(st, 0) + 1

    out = []
    out.append("# LangRef example coverage")
    out.append("")
    out.append(
        "Tests in this directory are derived from the illustrative `Example:` "
        "blocks of the LLVM Language Reference Manual (LLVM %s)." % version
    )
    out.append("")
    out.append(
        "Each test carries a `; langref:` line recording the section it came "
        "from and a hash of the example text as it read when the test was "
        "written. This file is generated by "
        "`utilities/langref_examples.py manifest`; after dropping a newer "
        "`langref.html` at the repo root, `utilities/langref_examples.py check` "
        "reports which examples have changed upstream."
    )
    out.append("")
    out.append(
        "A `gap` row is a test whose LangRef example Vellvm cannot currently "
        "meet: the assertion is present but written `;;ASSERT` so the harness "
        "skips it, next to a `VELLVM GAP` comment saying why."
    )
    out.append("")
    out.append(
        "%d instruction sections: %s."
        % (
            len(rows),
            ", ".join(
                "%d %s" % (counts[k], k) for k in sorted(counts)
            ),
        )
    )
    out.append("")
    out.append("| instruction | status | note |")
    out.append("| --- | --- | --- |")
    for name, st, note, anchor in rows:
        link = "[`%s`](%s#%s)" % (name, LANGREF_URL, anchor)
        out.append("| %s | %s | %s |" % (link, st, note))
    out.append("")
    path = os.path.join(OUTDIR, "MANIFEST.md")
    with open(path, "w", encoding="utf-8") as f:
        f.write("\n".join(out))
    return path, counts


# --------------------------------------------------------------------------
# commands


def cmd_generate(args):
    examples = parse_langref()
    version = llvm_version()
    os.makedirs(OUTDIR, exist_ok=True)
    written = skipped = 0
    for ex in examples.values():
        if os.path.exists(ex.path) and not args.force:
            skipped += 1
            continue
        with open(ex.path, "w", encoding="utf-8") as f:
            f.write(skeleton(ex, version))
        written += 1
    print("generate: %d written, %d left alone" % (written, skipped))
    return cmd_manifest(args)


def cmd_manifest(args):
    examples = parse_langref()
    path, counts = write_manifest(examples, llvm_version())
    print(
        "manifest: %s (%s)"
        % (
            os.path.relpath(path, REPO),
            ", ".join("%d %s" % (counts[k], k) for k in sorted(counts)),
        )
    )
    return 0


def cmd_check(args):
    """Compare each test's recorded provenance against the current LangRef."""
    examples = parse_langref()
    stale, orphan, unrecorded = [], [], []

    for ex in examples.values():
        if not os.path.exists(ex.path):
            if ex.name not in UNSUPPORTED:
                unrecorded.append(ex.name)
            continue
        with open(ex.path, encoding="utf-8") as f:
            body = f.read()
        m = PROVENANCE_RE.search(body)
        if m is None:
            unrecorded.append(ex.name)
        elif m.group("sha") != ex.sha:
            stale.append(ex.name)

    if os.path.isdir(OUTDIR):
        for fn in sorted(os.listdir(OUTDIR)):
            if fn.endswith(".ll") and fn[:-3] not in examples:
                orphan.append(fn[:-3])

    for names, msg in (
        (stale, "LangRef example changed since the test was written"),
        (unrecorded, "example has no test carrying a langref: provenance line"),
        (orphan, "test has no matching LangRef example section"),
    ):
        for n in sorted(names):
            print("%-16s %s" % (n, msg))

    bad = len(stale) + len(unrecorded) + len(orphan)
    print(
        "check: %d example section(s), %d issue(s)" % (len(examples), bad)
    )
    return 1 if bad else 0


def main():
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = p.add_subparsers(dest="cmd")
    g = sub.add_parser("generate", help="write skeleton tests")
    g.add_argument("--force", action="store_true", help="overwrite existing tests")
    g.set_defaults(fn=cmd_generate)
    m = sub.add_parser("manifest", help="regenerate MANIFEST.md")
    m.set_defaults(fn=cmd_manifest, force=False)
    c = sub.add_parser("check", help="report drift against langref.html")
    c.set_defaults(fn=cmd_check, force=False)
    args = p.parse_args()
    if not getattr(args, "fn", None):
        p.print_help()
        return 2
    if not os.path.exists(LANGREF):
        sys.exit("no such file: %s" % LANGREF)
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())
