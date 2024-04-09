
#!/bin/bash

compile_csmith() {
    # echo "Generating program: $1"
    clang -S -emit-llvm -O0 -o ./data/llO0/test$1.ll -I ./runtime ./data/c/test$1.c
    clang -S -emit-llvm -O1 -o ./data/llO1/test$1.ll -I ./runtime ./data/c/test$1.c
    clang -S -emit-llvm -O2 -o ./data/llO2/test$1.ll -I ./runtime ./data/c/test$1.c
    # echo "Generate test$1.c"
}

# Run the function in parallel for arguments 1 to 1000
max=1000
for i in $(seq 1 $max); do
    compile_csmith $i &
done

# Wait for all background processes to finish
wait
