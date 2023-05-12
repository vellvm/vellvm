#include<stdio.h>

int main(int argc, char** argv) {
  char str[] = "hello world\n";
  for (int i=0; i<12; i++) {
    printf("str[%d] = %d\n", i, (int)str[i]);
  }
  puts(str);
  printf("Addr of puts: %d\n", (int)&puts);
  printf("Addr of main: %d\n", (int)&main);
  return 0;
}
