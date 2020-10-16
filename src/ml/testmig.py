import sys

def create_assertion(simp):
    (path, name, ty, v) = simp
    return "; ASSERT_EQ: " + ty + " " + v + " = call " + ty + " @main()"  

def gen_assert(a):
    for asserter in a:
        print(asserter)

def parse_for_assertion(src, ty):
    # get rid of leading and trailing '[]'
    src = src.strip()
    contents = src[1:len(src) - 1].strip()
    raw_lines = contents.split(";")
    simplified = []
    for raw in raw_lines:
        raw = raw.strip()
        if raw == "":
            continue
        assertion = raw.split(",")
        f = assertion[0].strip()
        v = assertion[1].strip()
        f = f[1:]
        f = f[1:len(f) - 1]
        v = v[:len(v) - 1]
        paths = f.split("/")
        simplified.append((f, paths[len(paths) - 1], ty, v))
    return simplified

def lines_in_file(f, l_start, l_end):
    lines = ""
    linum = 0
    with open(f, 'r') as fh:
        for line in fh:
            linum += 1
            if l_start <= linum <= l_end:
                lines += line
    return lines
    
def main(args):
    l_start = int(args[0])
    l_end = int(args[1])
    ty = args[2]
    contents = lines_in_file("test.ml", l_start, l_end)
    p = parse_for_assertion(contents, ty)
    assertions = [create_assertion(i) for i in p]
    gen_assert(assertions)

if __name__ == "__main__":
    main(sys.argv[1:])
