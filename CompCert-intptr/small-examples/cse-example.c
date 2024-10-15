#include <stdlib.h>
#include <stdint.h>

int foo(long *p, long *q) {
  uintptr_t i = (uintptr_t) p;

  int c1 = ((void *)i < q);
  int c2 = (p < q);

  return c1 + c2;
}
