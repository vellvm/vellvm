#!/usr/bin/env bash

LL_FILE=${1%.bc}.ll

VELLVM_STDERR=$(mktemp)
VELLVM_STDOUT=$(mktemp)
EXECUTABLE=$(mktemp)

__cleanup()
{
    SIGNAL=$1

    [[ -f $LL_FILE ]] && rm "$LL_FILE"
    [[ -f $EXECUTABLE ]] && rm "$EXECUTABLE"
    [[ -f $VELLVM_STDERR ]] && rm "$VELLVM_STDERR"
    [[ -f $VELLVM_STDOUT ]] && rm "$VELLVM_STDOUT"

    if [[ -n $SIGNAL ]]
    then
        trap $SIGNAL
        kill -${SIGNAL} $$
    fi
}

trap __cleanup EXIT SIGHUP SIGINT SIGQUIT SIGABRT

llvm-dis $1 -o "$LL_FILE"
$VELLVM_EXE -interpret "$LL_INPUT" 2> "$VELLVM_STDERR" 1> "$VELLVM_STDOUT"
VELLVM_EXIT=$?

VELLVM_ERR=$(cat "$VELLVM_STDERR")
if [[ $VELLVM_EXIT != 0 ]]; then
    # Failure instead of return value, uninteresting test case.
    exit 0
fi

VELLVM_BUGPOINT_EXIT_CODE=$(perl -ne '/Program terminated with: .* (\d+)/ and printf $1' "$VELLVM_STDOUT")

# Compile with clang and get exit code...
$CLANG_EXE $LL_INPUT -o $EXECUTABLE
$EXECUTABLE
EXEC_BUGPOINT_EXIT_CODE=$?

if [[ $VELLVM_EXIT_CODE == $VELLVM_BUGPOINT_EXIT_CODE && $EXE_EXIT_CODE == $EXE_BUGPOINT_EXIT_CODE ]]; then
    exit 1
fi

exit 0
