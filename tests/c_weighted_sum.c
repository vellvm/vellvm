#include <inttypes.h>

int64_t ll_weighted_sum(int64_t a1, int64_t a2, int64_t a3, int64_t a4,
                        int64_t a5, int64_t a6, int64_t a7, int64_t a8) {
  int64_t sum = 0;
  sum += a1 * 1;
  sum += a2 * 2;
  sum += a3 * 3;
  sum += a4 * 4;
  sum += a5 * 5;
  sum += a6 * 6;
  sum += a7 * 7;
  sum += a8 * 8;
  return sum;
}
