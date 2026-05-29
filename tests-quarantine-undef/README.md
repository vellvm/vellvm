# Quarantined tests — `undef` keyword

The `.ll` files in this directory all contain the `undef` keyword. The
`ctrees-minimal` branch removed `undef` from the Vellvm semantics, and the
parser now raises an explicit error when it encounters `undef` (see
`src/ml/libvellvm/llvm_parser.mly`).

These tests were moved here to keep them out of the live test suite
(`src/ml` discovers `.ll` files via `find ../tests …`, which does not recurse
into this sibling directory).

When `undef` is reconciled with the minimal semantics — either restored,
mapped to `poison`, or otherwise replaced — these tests should be revisited
and either updated or reinstated into `../tests/`.
