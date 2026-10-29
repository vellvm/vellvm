#!/usr/bin/env python3
"""Fill in the <lineno> of `; ASSERT UB <n>: call <ty> @f(...)` from a
`; <- UB @f` marker on the instruction that should raise UB."""
import re, sys
for path in sys.argv[1:]:
    lines = open(path).read().split('\n')
    sites = {}
    for i, l in enumerate(lines, 1):
        for m in re.finditer(r';\s*<- UB\s+@([\w.$]+)', l):
            if m.group(1) in sites:
                sys.exit(f"{path}: duplicate marker for @{m.group(1)}")
            sites[m.group(1)] = i
    used = set()
    out = []
    for l in lines:
        m = re.match(r'(\s*;\s*ASSERT\s+UB\s+)(\d+|\?)(\s*:\s*call\s+.*?@([\w.$]+)\s*\(.*)$', l)
        if m:
            f = m.group(4)
            if f not in sites:
                sys.exit(f"{path}: no `; <- UB @{f}` marker")
            used.add(f)
            l = m.group(1) + str(sites[f]) + m.group(3)
        out.append(l)
    unused = set(sites) - used
    if unused:
        sys.exit(f"{path}: markers without assertions: {sorted(unused)}")
    open(path, 'w').write('\n'.join(out))
