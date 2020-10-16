import sys

def create_assertion(simp):
    (path, name, ty, v) = simp
    val = v
    if v == "qnan":
        val = "0x7FF0000000000001"
    if v == "snan":
        val = "0x7FF0000000000000"
    assertion = "; ASSERT_EQ: " + ty + " " + val + " = call " + ty + " @main(i64 0, i8** null)"  
    return (path, assertion)

def show_assert(a):
    for path in a:
        print("---" + path + "---")
        for cmt in a[path]:
            print(cmt)

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

def assertion_dict(assertions):
    dic = {}
    for (path, cmt) in assertions:
        if path in dic:
            dic[path].append(cmt)
        else:
            dic[path] = [cmt]
    return dic

def write_assertion(assertions):
    for path in assertions:
        asserts = assertions[path]
        with open("../" + path, 'a') as fh:
            fh.write("\n")
            for a in asserts:
                fh.write(a + "\n")
            fh.write("\n")
    
def main(args):
    l_start = int(args[0])
    l_end = int(args[1])
    ty = args[2]
    plan = args[3]
    contents = lines_in_file("test.ml", l_start, l_end)
    p = parse_for_assertion(contents, ty)
    assertions = assertion_dict([create_assertion(i) for i in p])
    if plan == "true": 
      show_assert(assertions)
    elif plan == "false":
      write_assertion(assertions)

if __name__ == "__main__":
    main(sys.argv[1:])
