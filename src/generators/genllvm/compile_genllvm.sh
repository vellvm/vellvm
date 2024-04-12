
#!/bin/bash

compile_genllvm() {
    # echo "Generating program: $1"
    base_name=$(basename $1) 
    cp $1 ./data/llO0
    # clang -S -emit-llvm -O0 --o ./data/llO0/test$1.ll -I ./runtime ./data/c/test$1.c
    clang -S -emit-llvm -O1 -o ./data/llO1/$base_name ./data/llO0/$base_name
    clang -S -emit-llvm -O2 -o ./data/llO2/$base_name ./data/llO0/$base_name
    # echo "Generate test$1.c"
}

# Run the function in parallel for arguments 1 to 1000

genllvm_dir="vellvm2-040b5ee6881de1b8f0d7eb4d736ecbf77869ddea"
mkdir ./data
mkdir ./data/llO0 ./data/llO1 ./data/llO2
pids=()
for file in ./$genllvm_dir/*; do
    compile_genllvm $file &
    pids+=($!)
    if (( ${#pids[@]} % 400 == 0 )); then
	echo "400 is met"
	wait ${pids[@]}
	pids=()
    fi
done
# Wait for all background processes to finish
wait
