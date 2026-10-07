#!/usr/bin/env bash
# Time each perf stress test with the built interpreter.
# Run from anywhere; uses the binary at src/vellvm.
set -u
here="$(cd "$(dirname "$0")" && pwd)"
src="$here/../../src"
vellvm="$src/vellvm"

if [ ! -x "$vellvm" ]; then
  echo "error: $vellvm not found or not executable; run 'make' in src/ first" >&2
  exit 1
fi

status=0
printf '%-22s %10s  %s\n' "test" "seconds" "assertions"
for f in "$here"/*.ll; do
  name="$(basename "$f")"
  start=$(python3 -c 'import time; print(time.monotonic())')
  # -L must precede -test-file: the -test* options stop argument processing.
  # libll supplies printf and friends, which some tests call.
  out="$(cd "$src" && ./vellvm -L libll -test-file "$f" 2>&1)"
  end=$(python3 -c 'import time; print(time.monotonic())')
  secs=$(python3 -c "print(f'{$end - $start:.2f}')")
  passed="$(printf '%s\n' "$out" | grep -E '^Passed:' || echo 'no result')"
  printf '%-22s %10s  %s\n' "$name" "$secs" "$passed"
  printf '%s\n' "$out" | grep -q '^Failed: 0/' || status=1
done
exit $status
