#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>
#include <stdint.h>

void print_x(int64_t v) {
  printf("x = %ld\n", (long) v);
}

void print_y(int64_t v) {
  printf("y = %ld\n", (long) v);
}

void print_z(int64_t v) {
  printf("z = %ld\n", (long) v);
}

extern void imp_command();

int main(int argc, char* argv[]) {
  imp_command();
  return 0;
}
