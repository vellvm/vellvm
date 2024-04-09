#!/bin/bash

gen_csmith() {
    echo "Generating program: $1"
    ./csmith > data/test$1.c
    echo "Generate test$1.c"
}

# Run the function in parallel for arguments 1 to 1000
max=1000
pids=()
for i in $(seq 1401 10000); do
    gen_csmith $i &
    pids+=($!)
    if (($i % 400 == 0)); then
	wait ${pids[@]}
	pids=()
    fi
done

# Wait for all background processes to finish
wait
