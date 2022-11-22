#!/usr/bin/env bash

LL_FILE=${1%.bc}.ll

__cleanup()
{
    SIGNAL=$1

    [[ -f $LL_FILE ]] && rm $LL_FILE

    if [ -n "$SIGNAL" ]
    then
        trap $SIGNAL
        kill -${SIGNAL} $$
    fi
}

trap __cleanup EXIT SIGHUP SIGINT SIGQUIT SIGABRT

llvm-dis $1 -o $LL_FILE
! $VELLVM_EXE -interpret $LL_FILE 2>&1 | grep $VELLVM_ERR
exit $?
