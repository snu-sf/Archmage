#include <stdlib.h>
#include <stdint.h>
long main (long sz, long temp) {
  void* p = (void *) malloc(sz - 10);
  uintptr_t i0 = (uintptr_t) p;
  uintptr_t i1 = i0;
  uintptr_t i2 = i1;
  uintptr_t i3 = (uintptr_t) p;
  uintptr_t i4 = (uintptr_t) p;
  uintptr_t i5 = (uintptr_t) p;
  uintptr_t i6 = (uintptr_t) p;
  uintptr_t i7 = (uintptr_t) p;
  long i8 = (long) p;
  long i9 = (long) p;
  long j0 = (long) p;
  long j1 = (long) p;
  long j2 = (long) p;
  long j3 = (long) p;
  long j4 = (long) p;
  long j5 = (long) p;
  long j6 = (long) p;
  long j7 = (long) p;
  long j8 = (long) p;
  long j9 = (long) p;

  long r =
  i0 +
  i1 +
  i2 +
  i3 +
  i4 +
  i5 +
  i6 +
  i7 +
  i8 +
  i9 +
  j0 +
  j1 +
  j2 +
  j3 +
  j4 +
  j5 +
  j6 +
  j7 +
  j8 + j9;

  return 100 + temp*temp + (temp-42) + r;
}
