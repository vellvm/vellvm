.PHONY: all test
all:
	../../../src/vellvm -l arrays.ll -l incomplete_arrays.ll -l packed_arrays.ll -l variable_arrays.ll -l ../../../src/libll/rust-intrinsics.ll -test-file array_tests.ll

test: all
