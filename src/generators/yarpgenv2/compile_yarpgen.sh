
#!/bin/bash

compile_yarpgen() {
    # echo "Generating program: $1"
    clang -S -emit-llvm -O0 -o ./data/llO0/driver1.ll -I ./runtime ./data/c/test$1/driver.c
    clang -S -emit-llvm -O0 -o ./data/llO0/func$1.ll -I ./runtime ./data/c/test$1/func.c
    clang -S -emit-llvm -O1 -o ./data/llO1/driver$1.ll -I ./runtime ./data/c/test$1/driver.c
    clang -S -emit-llvm -O1 -o ./data/llO1/func$1.ll -I ./runtime ./data/c/test$1/func.c
    clang -S -emit-llvm -O2 -o ./data/llO2/driver$1.ll -I ./runtime ./data/c/test$1/driver.c
    clang -S -emit-llvm -O2 -o ./data/llO2/func$1.ll -I ./runtime ./data/c/test$1/func.c
    # echo "Generate test$1.c"
}

# Run the function in parallel for arguments 1 to 1000
max=10
for i in $(seq 1 $max); do
    compile_yarpgen $i &
done

# Wait for all background processes to finish
wait
