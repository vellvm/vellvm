import os
import sys
from os.path import isfile, join
import subprocess


test_dir = sys.argv[1]
print(test_dir)


def files_in_dir(dir):
    return [dir + f for f in os.listdir(dir) if isfile(join(dir, f))]

def run_vellvm(file):
    print("Processing ", file)
    cmd = ['./vellvm', '--test-file', file]
    process = subprocess.Popen(cmd, stdout = subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines = True)
    stdout, stderr = process.communicate()
    return stdout + stderr
def decide_status(output):
    if "OK" in output:
        return ("PASSED", None)
    if "ERROR: not equal" in output:
        return ("FAILED", output[:400])
    if "Fatal error" in output:
        return ("EXCEPTION", output)
    if "Hidden" in output:
        return ("SUITE", None)
    return ("UNKNOWN", None)

def summarize(results):
    passed = 0
    failed = 0
    exception = 0
    suite = 0
    unknown = 0
    for (res, _) in results:
        if res == "PASSED":
            passed +=1
        elif res == "FAILED":
            failed += 1
        elif res == "EXCEPTION":
            exception += 1
        elif res == "SUITE":
            suite += 1
        else:
            unknown += 1
    return (passed, failed, exception, suite, unknown)

# takes a directory and a list of files and writes to a log file
def write_log(dir, files):
    results = []
    for f in files:
        result = run_vellvm(f)
        result = decide_status(result)
        results.append(result)
    (p, fa, ex, suite, unk) = summarize(results)
    numfiles = len(results)
    with open(dir + 'errlog', "w") as f:
        f.write(" -------------- Summary -----------------\n")
        f.write(" Files Passed: " + str(p) + "\n")
        f.write(" Files Failed: " + str(fa) + "\n")
        f.write(" Exceptions: " + str(ex) + "\n")
        f.write(" Hidden (limitations in test suite): " + str(suite) + "\n")
        f.write(" None of the above: " + str(unk) + "\n")
        f.write(" ----------------------------------------\n")
        zipped = zip(files,results)
        f.write(" -------------- Files that reported Passed -------------- \n\n" )
        for (fi, (res, meta)) in zipped:
            if res == "PASSED":
                f.write(fi + "\n")
        f.write("\n")
        f.write(" -------------- Files that reported Hidden -------------- \n\n" )
        for (fi, (res, meta)) in zipped:
            if res == "SUITE":
                f.write(fi + "\n")
        f.write("Vighnesh look at this \n\n")
        f.write(" -------------- Files that triggered failures ------------- \n" )
        f.write(" -------------- Writing first 500 chars of failure -------- \n\n" )
        for (fi, (res, meta)) in zipped:
            if res == "FAILED":
                f.write(fi+ ":\n")
                f.write(">>>>>>>>>>>>>>>>>>>> \n")
                f.write(meta)
                f.write("<<<<<<<<<<<<<<< \n\n")
        f.write(" -------------- Files that triggered Exceptions ------------ \n")
        f.write(" -------------- Writing stderr                  ------------ \n\n")
        for (fi, (res,meta)) in zipped:
            if res == "EXCEPTION":
                f.write(fi+ ":\n")
                f.write(">>>>>>>>>>>>>>>>>>>> \n")
                f.write(meta)
                f.write("<<<<<<<<<<<<<<< \n\n")
        f.write(" -------------- Files that didn't trigger any of the above ----- \n\n")
        for (fi, (res, meta)) in zipped:
            if res == "UNKNOWN":
                f.write(fi + "\n")
        f.write("--------------           END REPORT ---------------------------  \n")
        f.close()
    
        
files_to_test = files_in_dir(test_dir)
write_log(test_dir, files_to_test)
