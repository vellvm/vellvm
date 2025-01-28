#! /usr/bin/env bash

# Takes all tests which use (non-opaque) pointers in a directory
# and make all pointers opaque.
# If you want to update in place, just set `target_dir="$src_dir"`.
# This unfortunately only works for "simple" pointee types; in particular,
# pointers to array (e.g. [3 x i8]*) are not picked up...

root="../.."
# Tests to potentially convert
src_dir="$root"/tests/ll
# Output directory; the directory structure from the source will be preserved.
target_dir="$root"/tests/opaque-ptrs

ptr_regex="%?[-$._[:alpha:][:digit:]]+\*+"
files=$(cd "$src_dir" && grep -rl --include \*.ll -E "$ptr_regex")

for file in $files; do
  src="$src_dir"/"$file"
  target="$target_dir"/"$file"
  mkdir -p "$(dirname "$target")"
  sed -E "s/$ptr_regex/ptr/g" "$src" > "$target" 
done
